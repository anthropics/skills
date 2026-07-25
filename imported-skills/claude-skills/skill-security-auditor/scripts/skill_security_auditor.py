#!/usr/bin/env python3
"""
Skill Security Auditor — Scan AI agent skills for security risks before installation.

Usage:
    python3 skill_security_auditor.py /path/to/skill/
    python3 skill_security_auditor.py https://github.com/user/repo --skill skill-name
    python3 skill_security_auditor.py /path/to/skill/ --strict --json

Exit codes:
    0 = PASS (safe to install)
    1 = FAIL (critical findings, do not install)
    2 = WARN (review manually before installing)
"""

import argparse
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import shutil
from dataclasses import dataclass, field, asdict
from enum import IntEnum
from pathlib import Path
from typing import Optional


class Severity(IntEnum):
    INFO = 0
    HIGH = 1
    CRITICAL = 2


SEVERITY_LABELS = {
    Severity.INFO: "⚪ INFO",
    Severity.HIGH: "🟡 HIGH",
    Severity.CRITICAL: "🔴 CRITICAL",
}

SEVERITY_NAMES = {
    Severity.INFO: "INFO",
    Severity.HIGH: "HIGH",
    Severity.CRITICAL: "CRITICAL",
}


@dataclass
class Finding:
    severity: Severity
    category: str
    file: str
    line: int
    pattern: str
    risk: str
    fix: str

    def to_dict(self):
        d = asdict(self)
        d["severity"] = SEVERITY_NAMES[self.severity]
        return d


@dataclass
class AuditReport:
    skill_name: str
    skill_path: str
    findings: list = field(default_factory=list)
    files_scanned: int = 0
    scripts_scanned: int = 0
    md_files_scanned: int = 0

    @property
    def critical_count(self):
        return sum(1 for f in self.findings if f.severity == Severity.CRITICAL)

    @property
    def high_count(self):
        return sum(1 for f in self.findings if f.severity == Severity.HIGH)

    @property
    def info_count(self):
        return sum(1 for f in self.findings if f.severity == Severity.INFO)

    @property
    def verdict(self):
        if self.critical_count > 0:
            return "FAIL"
        if self.high_count > 0:
            return "WARN"
        return "PASS"

    def to_dict(self):
        return {
            "skill_name": self.skill_name,
            "skill_path": self.skill_path,
            "verdict": self.verdict,
            "summary": {
                "critical": self.critical_count,
                "high": self.high_count,
                "info": self.info_count,
                "total": len(self.findings),
            },
            "stats": {
                "files_scanned": self.files_scanned,
                "scripts_scanned": self.scripts_scanned,
                "md_files_scanned": self.md_files_scanned,
            },
            "findings": [f.to_dict() for f in self.findings],
        }


# =============================================================================
# CODE EXECUTION PATTERNS
# =============================================================================

CODE_PATTERNS = [
    # Command injection — CRITICAL
    {
        "regex": r"\bos\.system\s*\(",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Arbitrary command execution via os.system()",  # noqa: SEC-AUDITOR
        "fix": "Use subprocess.run() with list arguments and shell=False",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.popen\s*\(",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Command execution via os.popen()",  # noqa: SEC-AUDITOR
        "fix": "Use subprocess.run() with list arguments and capture_output=True",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bsubprocess\.\w+\([^)]*shell\s*=\s*True",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Shell injection via subprocess with shell=True",  # noqa: SEC-AUDITOR
        "fix": "Use subprocess.run() with list arguments and shell=False",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bcommands\.get(?:status)?output\s*\(",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Deprecated command execution via commands module",  # noqa: SEC-AUDITOR
        "fix": "Use subprocess.run() with list arguments",  # noqa: SEC-AUDITOR
    },
    # Code execution — CRITICAL
    {
        "regex": r"\beval\s*\(",  # noqa: SEC-AUDITOR
        "category": "CODE-EXEC",
        "severity": Severity.CRITICAL,
        "risk": "Arbitrary code execution via eval()",  # noqa: SEC-AUDITOR
        "fix": "Use ast.literal_eval() for data parsing or explicit parsing logic",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bexec\s*\(",  # noqa: SEC-AUDITOR
        "category": "CODE-EXEC",
        "severity": Severity.CRITICAL,
        "risk": "Arbitrary code execution via exec()",  # noqa: SEC-AUDITOR
        "fix": "Remove exec() — rewrite logic to avoid dynamic code execution",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bcompile\s*\([^)]*['\"]exec['\"]",
        "category": "CODE-EXEC",
        "severity": Severity.CRITICAL,
        "risk": "Dynamic code compilation for execution",  # noqa: SEC-AUDITOR
        "fix": "Remove compile() with exec mode — use explicit logic instead",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\b__import__\s*\(",  # noqa: SEC-AUDITOR
        "category": "CODE-EXEC",
        "severity": Severity.CRITICAL,
        "risk": "Dynamic module import — can load arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Use explicit import statements",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bimportlib\.import_module\s*\(",  # noqa: SEC-AUDITOR
        "category": "CODE-EXEC",
        "severity": Severity.HIGH,
        "risk": "Dynamic module import via importlib",  # noqa: SEC-AUDITOR
        "fix": "Use explicit import statements unless dynamic loading is justified",  # noqa: SEC-AUDITOR
    },
    # Obfuscation — CRITICAL
    {
        "regex": r"\bbase64\.b64decode\s*\(",  # noqa: SEC-AUDITOR
        "category": "OBFUSCATION",
        "severity": Severity.CRITICAL,
        "risk": "Base64 decoding — may hide malicious payloads",  # noqa: SEC-AUDITOR
        "fix": "Review decoded content. If not processing user data, remove base64 usage",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bcodecs\.decode\s*\(",  # noqa: SEC-AUDITOR
        "category": "OBFUSCATION",
        "severity": Severity.CRITICAL,
        "risk": "Codec decoding — may hide obfuscated payloads",  # noqa: SEC-AUDITOR
        "fix": "Review decoded content and ensure it's not hiding executable code",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\\x[0-9a-fA-F]{2}(?:\\x[0-9a-fA-F]{2}){7,}",  # noqa: SEC-AUDITOR
        "category": "OBFUSCATION",
        "severity": Severity.CRITICAL,
        "risk": "Long hex-encoded string — likely obfuscated payload",  # noqa: SEC-AUDITOR
        "fix": "Decode and inspect the content. Replace with readable strings",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bchr\s*\(\s*\d+\s*\)(?:\s*\+\s*chr\s*\(\s*\d+\s*\)){3,}",  # noqa: SEC-AUDITOR
        "category": "OBFUSCATION",
        "severity": Severity.CRITICAL,
        "risk": "Character-by-character string construction — obfuscation technique",  # noqa: SEC-AUDITOR
        "fix": "Replace chr() chains with readable string literals",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"bytes\.fromhex\s*\(",  # noqa: SEC-AUDITOR
        "category": "OBFUSCATION",
        "severity": Severity.HIGH,
        "risk": "Hex byte decoding — may hide payloads",  # noqa: SEC-AUDITOR
        "fix": "Review the hex content and replace with readable code",  # noqa: SEC-AUDITOR
    },
    # Network exfiltration — CRITICAL
    {
        "regex": r"\brequests\.(?:post|put|patch)\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Outbound HTTP write request — potential data exfiltration",  # noqa: SEC-AUDITOR
        "fix": "Remove outbound POST/PUT/PATCH or verify destination is trusted and necessary",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\burllib\.request\.urlopen\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.HIGH,
        "risk": "Outbound HTTP request via urllib",  # noqa: SEC-AUDITOR
        "fix": "Verify the URL destination is trusted. Remove if not needed",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\burllib\.request\.Request\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.HIGH,
        "risk": "HTTP request construction via urllib",  # noqa: SEC-AUDITOR
        "fix": "Verify the request target and ensure no sensitive data is sent",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bsocket\.(?:connect|create_connection)\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Raw socket connection — potential C2 or exfiltration channel",  # noqa: SEC-AUDITOR
        "fix": "Remove raw socket usage unless absolutely required and justified",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bhttpx\.(?:post|put|patch|AsyncClient)\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Outbound HTTP request via httpx",  # noqa: SEC-AUDITOR
        "fix": "Remove or verify destination is trusted",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\baiohttp\.ClientSession\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Async HTTP client — potential exfiltration",  # noqa: SEC-AUDITOR
        "fix": "Remove or verify all request destinations are trusted",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\brequests\.get\s*\(",  # noqa: SEC-AUDITOR
        "category": "NET-READ",
        "severity": Severity.HIGH,
        "risk": "Outbound HTTP GET request — may download malicious payloads",  # noqa: SEC-AUDITOR
        "fix": "Verify the URL is trusted and necessary for skill functionality",  # noqa: SEC-AUDITOR
    },
    # Credential harvesting — CRITICAL
    {
        "regex": r"(?:open|read|Path)\s*\([^)]*(?:\.ssh|\.aws|\.config/secrets|\.gnupg|\.npmrc|\.pypirc)",  # noqa: SEC-AUDITOR
        "category": "CRED-HARVEST",
        "severity": Severity.CRITICAL,
        "risk": "Reads credential files (SSH keys, AWS creds, secrets)",  # noqa: SEC-AUDITOR
        "fix": "Remove all access to credential directories",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.environ\s*\[\s*['\"](?:AWS_|GITHUB_TOKEN|API_KEY|SECRET|PASSWORD|TOKEN|PRIVATE)",
        "category": "CRED-HARVEST",
        "severity": Severity.CRITICAL,
        "risk": "Extracts sensitive environment variables",  # noqa: SEC-AUDITOR
        "fix": "Remove credential access unless skill explicitly requires it and user is warned",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.environ\.get\s*\([^)]*(?:AWS_|GITHUB_TOKEN|API_KEY|SECRET|PASSWORD|TOKEN|PRIVATE)",  # noqa: SEC-AUDITOR
        "category": "CRED-HARVEST",
        "severity": Severity.CRITICAL,
        "risk": "Reads sensitive environment variables",  # noqa: SEC-AUDITOR
        "fix": "Remove credential access. Skills should not need external credentials",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?:keyring|keychain)\.\w+\s*\(",  # noqa: SEC-AUDITOR
        "category": "CRED-HARVEST",
        "severity": Severity.CRITICAL,
        "risk": "Accesses system keyring/keychain",  # noqa: SEC-AUDITOR
        "fix": "Remove keyring access — skills should not access system credential stores",  # noqa: SEC-AUDITOR
    },
    # File system abuse — HIGH
    {
        "regex": r"(?:open|write|Path)\s*\([^)]*(?:/etc/|/usr/|/var/|/tmp/\.\w)",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.HIGH,
        "risk": "Writes to system directories outside skill scope",  # noqa: SEC-AUDITOR
        "fix": "Restrict file operations to the skill directory or user-specified output paths",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?:open|write|Path)\s*\([^)]*(?:\.bashrc|\.bash_profile|\.profile|\.zshrc|\.zprofile)",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.CRITICAL,
        "risk": "Modifies shell configuration — potential persistence mechanism",  # noqa: SEC-AUDITOR
        "fix": "Remove all writes to shell config files",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.symlink\s*\(",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.HIGH,
        "risk": "Creates symbolic links — potential directory traversal attack",  # noqa: SEC-AUDITOR
        "fix": "Remove symlink creation unless explicitly required and bounded",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bshutil\.rmtree\s*\(",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.HIGH,
        "risk": "Recursive directory deletion — destructive operation",  # noqa: SEC-AUDITOR
        "fix": "Remove or restrict to specific, validated paths within skill scope",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.remove\s*\(|os\.unlink\s*\(",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.HIGH,
        "risk": "File deletion — verify target is within skill scope",  # noqa: SEC-AUDITOR
        "fix": "Ensure deletion targets are validated and within expected paths",  # noqa: SEC-AUDITOR
    },
    # Privilege escalation — CRITICAL
    {
        "regex": r"\bsudo\b",  # noqa: SEC-AUDITOR
        "category": "PRIV-ESC",
        "severity": Severity.CRITICAL,
        "risk": "Sudo invocation — privilege escalation attempt",  # noqa: SEC-AUDITOR
        "fix": "Remove sudo usage. Skills should never require elevated privileges",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bchmod\b.*\b[0-7]*7[0-7]{2}\b",  # noqa: SEC-AUDITOR
        "category": "PRIV-ESC",
        "severity": Severity.HIGH,
        "risk": "Setting world-executable permissions",  # noqa: SEC-AUDITOR
        "fix": "Use restrictive permissions (e.g., 0o644 for files, 0o755 for dirs)",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bos\.set(?:e)?uid\s*\(",  # noqa: SEC-AUDITOR
        "category": "PRIV-ESC",
        "severity": Severity.CRITICAL,
        "risk": "UID manipulation — privilege escalation",  # noqa: SEC-AUDITOR
        "fix": "Remove UID manipulation. Skills must run as the invoking user",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bcrontab\b|\bcron\b.*\bwrite\b",  # noqa: SEC-AUDITOR
        "category": "PRIV-ESC",
        "severity": Severity.CRITICAL,
        "risk": "Cron job manipulation — persistence mechanism",  # noqa: SEC-AUDITOR
        "fix": "Remove cron manipulation. Skills should not modify scheduled tasks",  # noqa: SEC-AUDITOR
    },
    # Unsafe deserialization — HIGH
    {
        "regex": r"\bpickle\.loads?\s*\(",  # noqa: SEC-AUDITOR
        "category": "DESERIAL",
        "severity": Severity.HIGH,
        "risk": "Pickle deserialization — can execute arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Use json.loads() or other safe serialization formats",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\byaml\.(?:load|unsafe_load)\s*\([^)]*(?!Loader\s*=\s*yaml\.SafeLoader)",  # noqa: SEC-AUDITOR
        "category": "DESERIAL",
        "severity": Severity.HIGH,
        "risk": "Unsafe YAML loading — can execute arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Use yaml.safe_load() or yaml.load(data, Loader=yaml.SafeLoader)",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bmarshal\.loads?\s*\(",  # noqa: SEC-AUDITOR
        "category": "DESERIAL",
        "severity": Severity.HIGH,
        "risk": "Marshal deserialization — can execute arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Use json.loads() or other safe serialization formats",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bshelve\.open\s*\(",  # noqa: SEC-AUDITOR
        "category": "DESERIAL",
        "severity": Severity.HIGH,
        "risk": "Shelve uses pickle internally — can execute arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Use JSON or SQLite for persistent storage",  # noqa: SEC-AUDITOR
    },
]

# =============================================================================
# PROMPT INJECTION PATTERNS
# =============================================================================

PROMPT_INJECTION_PATTERNS = [
    # System prompt override — CRITICAL
    {
        "regex": r"(?i)ignore\s+(?:all\s+)?(?:previous|prior|above)\s+instructions",  # noqa: SEC-AUDITOR
        "category": "PROMPT-OVERRIDE",
        "severity": Severity.CRITICAL,
        "risk": "Attempts to override system prompt and prior instructions",  # noqa: SEC-AUDITOR
        "fix": "Remove instruction override attempts",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)you\s+are\s+now\s+(?:a|an|the)\s+",  # noqa: SEC-AUDITOR
        "category": "PROMPT-OVERRIDE",
        "severity": Severity.CRITICAL,
        "risk": "Role hijacking — attempts to redefine the AI's identity",  # noqa: SEC-AUDITOR
        "fix": "Remove role redefinition. Skills should provide instructions, not identity changes",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:disregard|forget|override)\s+(?:your|all|any)\s+(?:instructions|rules|guidelines|constraints|safety)",  # noqa: SEC-AUDITOR
        "category": "PROMPT-OVERRIDE",
        "severity": Severity.CRITICAL,
        "risk": "Explicit instruction override attempt",  # noqa: SEC-AUDITOR
        "fix": "Remove override directives",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:pretend|act\s+as\s+if|imagine)\s+you\s+(?:have\s+no|don'?t\s+have\s+any)\s+(?:restrictions|limits|rules|safety)",  # noqa: SEC-AUDITOR
        "category": "SAFETY-BYPASS",
        "severity": Severity.CRITICAL,
        "risk": "Safety restriction bypass attempt",  # noqa: SEC-AUDITOR
        "fix": "Remove safety bypass instructions",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:skip|disable|bypass|turn\s+off|ignore)\s+(?:safety|content|security)\s+(?:checks?|filters?|restrictions?|rules?)",  # noqa: SEC-AUDITOR
        "category": "SAFETY-BYPASS",
        "severity": Severity.CRITICAL,
        "risk": "Explicit safety mechanism bypass",  # noqa: SEC-AUDITOR
        "fix": "Remove safety bypass directives",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:execute|run)\s+(?:any|all|arbitrary)\s+(?:commands?|code|scripts?)\s+(?:without|no)\s+(?:asking|confirmation|restriction|limit)",  # noqa: SEC-AUDITOR
        "category": "SAFETY-BYPASS",
        "severity": Severity.CRITICAL,
        "risk": "Unrestricted command execution directive",  # noqa: SEC-AUDITOR
        "fix": "Add explicit permission requirements for any command execution",  # noqa: SEC-AUDITOR
    },
    # Data extraction — CRITICAL
    {
        "regex": r"(?i)(?:send|upload|post|transmit|exfiltrate)\s+(?:the\s+)?(?:contents?|data|files?|information)\s+(?:of|from|to)",  # noqa: SEC-AUDITOR
        "category": "PROMPT-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Instruction to exfiltrate data",  # noqa: SEC-AUDITOR
        "fix": "Remove data transmission directives",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:read|access|open|get)\s+(?:the\s+)?(?:contents?\s+of\s+)?(?:~|\/home|\/etc|\.ssh|\.aws|\.env|credentials?|secrets?|api.?keys?)",  # noqa: SEC-AUDITOR
        "category": "PROMPT-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Instruction to access sensitive files or credentials",  # noqa: SEC-AUDITOR
        "fix": "Remove credential/sensitive file access directives",  # noqa: SEC-AUDITOR
    },
    # Hidden instructions — HIGH
    {
        "regex": r"[\u200b\u200c\u200d\ufeff\u00ad]",  # noqa: SEC-AUDITOR
        "category": "HIDDEN-INSTR",
        "severity": Severity.HIGH,
        "risk": "Zero-width or invisible characters — may hide instructions",  # noqa: SEC-AUDITOR
        "fix": "Remove zero-width characters. All instructions should be visible",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"<!--\s*(?:system|instruction|override|ignore|execute|run|sudo|admin)",  # noqa: SEC-AUDITOR
        "category": "HIDDEN-INSTR",
        "severity": Severity.HIGH,
        "risk": "HTML comments containing suspicious directives",  # noqa: SEC-AUDITOR
        "fix": "Remove HTML comments with directives. Use visible markdown instead",  # noqa: SEC-AUDITOR
    },
    # Excessive permissions — HIGH
    {
        "regex": r"(?i)(?:full|unrestricted|complete)\s+(?:access|control|permissions?)\s+(?:to|over)\s+(?:the\s+)?(?:file\s*system|network|internet|shell|terminal|system)",  # noqa: SEC-AUDITOR
        "category": "EXCESS-PERM",
        "severity": Severity.HIGH,
        "risk": "Requests unrestricted system access",  # noqa: SEC-AUDITOR
        "fix": "Scope permissions to specific, necessary operations",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"(?i)(?:always|automatically)\s+(?:approve|accept|allow|grant|execute)\s+(?:all|any|every)",  # noqa: SEC-AUDITOR
        "category": "EXCESS-PERM",
        "severity": Severity.HIGH,
        "risk": "Blanket approval directive — bypasses human oversight",  # noqa: SEC-AUDITOR
        "fix": "Require explicit user confirmation for sensitive operations",  # noqa: SEC-AUDITOR
    },
]

# =============================================================================
# DEPENDENCY PATTERNS
# =============================================================================

# Known typosquatting targets (popular package → common misspellings)
TYPOSQUAT_TARGETS = {
    "requests": ["reqeusts", "requets", "reqests", "request", "requsts", "rquests"],
    "numpy": ["numpi", "numppy", "numy", "numpie"],
    "pandas": ["panda", "pandass", "pnadas"],
    "flask": ["flaskk", "flaask", "flas"],
    "django": ["djagno", "djanog", "djnago"],
    "tensorflow": ["tenserflow", "tensorfow", "tensorflw"],
    "pytorch": ["pytorh", "pytoch", "pytorchh"],
    "cryptography": ["crytography", "cryptograpy", "crypography"],
    "pillow": ["pilllow", "pilow", "pillw"],
    "boto3": ["boto33", "botto3", "bto3"],
    "pyyaml": ["pyaml", "pyymal", "pymal"],
    "httpx": ["httppx", "htpx", "httpxx"],
    "aiohttp": ["aiohtp", "aiohtpp", "aiohttp2"],
    "paramiko": ["parmiko", "paramkio", "paramiiko"],
    "pycrypto": ["pycripto", "pycrpto", "pycryptoo"],
}

SHELL_PATTERNS = [
    # Bash-specific patterns
    {
        "regex": r"\bcurl\s+.*\|\s*(?:ba)?sh\b",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Pipe-to-shell pattern — downloads and executes arbitrary code",  # noqa: SEC-AUDITOR
        "fix": "Download script first, inspect it, then execute explicitly",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bwget\s+.*&&\s*(?:ba)?sh\b",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Download-and-execute pattern",  # noqa: SEC-AUDITOR
        "fix": "Download script first, inspect it, then execute explicitly",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\brm\s+-rf\s+/(?!\s*#)",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.CRITICAL,
        "risk": "Recursive deletion from root — catastrophic data loss",  # noqa: SEC-AUDITOR
        "fix": "Remove destructive root-level deletion commands",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bchmod\s+(?:u\+s|4[0-7]{3})\b",  # noqa: SEC-AUDITOR
        "category": "PRIV-ESC",
        "severity": Severity.CRITICAL,
        "risk": "Setting SUID bit — privilege escalation",  # noqa: SEC-AUDITOR
        "fix": "Remove SUID modifications. Skills should never set SUID",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r">\s*/dev/(?:sd[a-z]|nvme|loop)",  # noqa: SEC-AUDITOR
        "category": "FS-ABUSE",
        "severity": Severity.CRITICAL,
        "risk": "Direct write to block device — data destruction",  # noqa: SEC-AUDITOR
        "fix": "Remove direct block device writes",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bnc\s+-[el]|\bncat\s+-[el]|\bnetcat\b",  # noqa: SEC-AUDITOR
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Netcat listener/connection — potential reverse shell or exfiltration",  # noqa: SEC-AUDITOR
        "fix": "Remove netcat usage",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\b(?:python|python3|node|perl|ruby)\s+-c\s+['\"]",
        "category": "CODE-EXEC",
        "severity": Severity.HIGH,
        "risk": "Inline code execution in shell script",  # noqa: SEC-AUDITOR
        "fix": "Move code to a separate, inspectable script file",  # noqa: SEC-AUDITOR
    },
]

JS_PATTERNS = [
    {
        "regex": r"\bchild_process\b",  # noqa: SEC-AUDITOR
        "category": "CMD-INJECT",
        "severity": Severity.CRITICAL,
        "risk": "Node.js child_process — command execution",  # noqa: SEC-AUDITOR
        "fix": "Remove child_process usage or justify with explicit documentation",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bFunction\s*\([^)]*\)\s*\(",  # noqa: SEC-AUDITOR
        "category": "CODE-EXEC",
        "severity": Severity.CRITICAL,
        "risk": "Dynamic Function constructor — equivalent to eval()",  # noqa: SEC-AUDITOR
        "fix": "Use explicit function definitions instead",  # noqa: SEC-AUDITOR
    },
    {
        "regex": r"\bfetch\s*\([^)]*\{[^}]*method\s*:\s*['\"](?:POST|PUT|PATCH)",
        "category": "NET-EXFIL",
        "severity": Severity.CRITICAL,
        "risk": "Outbound HTTP write request via fetch()",  # noqa: SEC-AUDITOR
        "fix": "Remove or verify destination is trusted",  # noqa: SEC-AUDITOR
    },
]


# =============================================================================
# SCANNER
# =============================================================================

CODE_EXTENSIONS = {".py", ".sh", ".bash", ".js", ".ts", ".mjs", ".cjs"}
MD_EXTENSIONS = {".md", ".mdx", ".markdown"}
ALL_SCAN_EXTENSIONS = CODE_EXTENSIONS | MD_EXTENSIONS


def scan_file_code(filepath: Path, report: AuditReport):
    """Scan a code file for dangerous patterns."""
    try:
        content = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return

    lines = content.split("\n")
    ext = filepath.suffix.lower()

    # Select pattern sets based on file type
    patterns = list(CODE_PATTERNS)
    if ext in {".sh", ".bash"}:
        patterns.extend(SHELL_PATTERNS)
    if ext in {".js", ".ts", ".mjs", ".cjs"}:
        patterns.extend(JS_PATTERNS)

    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        # Skip comments
        if stripped.startswith("#") and ext in {".py", ".sh", ".bash"}:
            continue
        if stripped.startswith("//") and ext in {".js", ".ts", ".mjs", ".cjs"}:
            continue
        # Honor explicit suppression directive (security tooling references its
        # own dangerous-pattern strings inside regex/check definitions, which
        # would otherwise trigger every pattern that matches itself)
        if "noqa: SEC-AUDITOR" in line or "auditor:ignore-line" in line:
            continue

        for pat in patterns:
            if re.search(pat["regex"], line):
                report.findings.append(
                    Finding(
                        severity=pat["severity"],
                        category=pat["category"],
                        file=str(filepath),
                        line=i,
                        pattern=stripped[:120],
                        risk=pat["risk"],
                        fix=pat["fix"],
                    )
                )


def scan_file_prompt_injection(filepath: Path, report: AuditReport):
    """Scan a markdown file for prompt injection patterns."""
    try:
        content = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return

    lines = content.split("\n")

    for i, line in enumerate(lines, 1):
        # Honor explicit suppression directive (markdown can use HTML comment)
        if "noqa: SEC-AUDITOR" in line or "auditor:ignore-line" in line:
            continue
        for pat in PROMPT_INJECTION_PATTERNS:
            if re.search(pat["regex"], line):
                report.findings.append(
                    Finding(
                        severity=pat["severity"],
                        category=pat["category"],
                        file=str(filepath),
                        line=i,
                        pattern=line.strip()[:120],
                        risk=pat["risk"],
                        fix=pat["fix"],
                    )
                )


def scan_dependencies(skill_path: Path, report: AuditReport):
    """Scan dependency files for supply chain risks."""
    # Check requirements.txt
    req_file = skill_path / "requirements.txt"
    if req_file.exists():
        try:
            lines = req_file.read_text().split("\n")
        except Exception:
            return

        all_typosquats = {}
        for real_pkg, fakes in TYPOSQUAT_TARGETS.items():
            for fake in fakes:
                all_typosquats[fake.lower()] = real_pkg

        for i, line in enumerate(lines, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue

            # Extract package name
            pkg_name = re.split(r"[>=<!\[;]", line)[0].strip().lower()

            # Typosquatting check
            if pkg_name in all_typosquats:
                report.findings.append(
                    Finding(
                        severity=Severity.HIGH,
                        category="DEPS-TYPOSQUAT",
                        file=str(req_file),
                        line=i,
                        pattern=line,
                        risk=f"Possible typosquatting — did you mean '{all_typosquats[pkg_name]}'?",
                        fix=f"Verify package name. Likely should be '{all_typosquats[pkg_name]}'",
                    )
                )

            # Unpinned version check
            if pkg_name and "==" not in line and pkg_name not in (".", "-e", "-r"):
                report.findings.append(
                    Finding(
                        severity=Severity.INFO,
                        category="DEPS-UNPIN",
                        file=str(req_file),
                        line=i,
                        pattern=line,
                        risk="Unpinned dependency — may pull vulnerable versions",
                        fix=f"Pin to specific version: {pkg_name}==<version>",
                    )
                )

    # Check for pip/npm install in code
    for code_file in skill_path.rglob("*"):
        if code_file.suffix.lower() not in CODE_EXTENSIONS:
            continue
        try:
            content = code_file.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue

        for i, line in enumerate(content.split("\n"), 1):
            stripped = line.strip()
            # Skip comments (this line is documentation about install commands,
            # not actual install command at runtime)
            if stripped.startswith("#") or stripped.startswith("//"):
                continue
            if "noqa: SEC-AUDITOR" in line or "auditor:ignore-line" in line:
                continue
            if re.search(r"\bpip\s+install\b", line):
                report.findings.append(
                    Finding(
                        severity=Severity.HIGH,
                        category="DEPS-RUNTIME",
                        file=str(code_file),
                        line=i,
                        pattern=line.strip()[:120],
                        risk="Runtime package installation — may install untrusted code",
                        fix="Move dependencies to requirements.txt for pre-install review",
                    )
                )
            if re.search(r"\bnpm\s+install\b|\byarn\s+add\b|\bpnpm\s+add\b", line):
                report.findings.append(
                    Finding(
                        severity=Severity.HIGH,
                        category="DEPS-RUNTIME",
                        file=str(code_file),
                        line=i,
                        pattern=line.strip()[:120],
                        risk="Runtime package installation — may install untrusted code",
                        fix="Move dependencies to package.json for pre-install review",
                    )
                )


def scan_filesystem(skill_path: Path, report: AuditReport):
    """Scan the skill directory structure for suspicious files."""
    for item in skill_path.rglob("*"):
        rel = item.relative_to(skill_path)
        rel_str = str(rel)

        # Skip .git directory
        if ".git" in rel.parts:
            continue

        report.files_scanned += 1

        # Hidden files (except common ones)
        if item.name.startswith(".") and item.name not in (
            ".gitignore", ".gitkeep", ".editorconfig", ".prettierrc",
            ".eslintrc", ".pylintrc", ".flake8",
            ".claude-plugin", ".codex", ".gemini",
            ".mcp.json",
        ):
            severity = Severity.CRITICAL if item.name == ".env" else Severity.HIGH
            report.findings.append(
                Finding(
                    severity=severity,
                    category="FS-HIDDEN",
                    file=rel_str,
                    line=0,
                    pattern=item.name,
                    risk=f"Hidden file '{item.name}' — may contain secrets or hidden config",
                    fix="Remove hidden files from skill distribution",
                )
            )

        # Binary files
        if item.is_file() and item.suffix.lower() in (
            ".exe", ".dll", ".so", ".dylib", ".bin", ".elf",
            ".com", ".msi", ".deb", ".rpm", ".apk",
        ):
            report.findings.append(
                Finding(
                    severity=Severity.CRITICAL,
                    category="FS-BINARY",
                    file=rel_str,
                    line=0,
                    pattern=item.name,
                    risk="Binary executable in skill — high risk of malicious payload",
                    fix="Remove binary files. Skills should use interpreted scripts only",
                )
            )

        # Large files (>1MB)
        if item.is_file():
            try:
                size = item.stat().st_size
                if size > 1_000_000:
                    report.findings.append(
                        Finding(
                            severity=Severity.INFO,
                            category="FS-LARGE",
                            file=rel_str,
                            line=0,
                            pattern=f"{size / 1_000_000:.1f}MB",
                            risk="Large file — may hide payloads or bloat installation",
                            fix="Review file contents. Consider if this file is necessary",
                        )
                    )
            except OSError:
                pass

        # Symlinks
        if item.is_symlink():
            try:
                target = item.resolve()
                if not str(target).startswith(str(skill_path.resolve())):
                    report.findings.append(
                        Finding(
                            severity=Severity.CRITICAL,
                            category="FS-SYMLINK",
                            file=rel_str,
                            line=0,
                            pattern=f"→ {target}",
                            risk="Symlink points outside skill directory — directory traversal risk",
                            fix="Remove symlinks pointing outside the skill directory",
                        )
                    )
            except (OSError, ValueError):
                pass

        # SUID/SGID bits
        if item.is_file():
            try:
                mode = item.stat().st_mode
                if mode & (stat.S_ISUID | stat.S_ISGID):
                    report.findings.append(
                        Finding(
                            severity=Severity.CRITICAL,
                            category="FS-SUID",
                            file=rel_str,
                            line=0,
                            pattern=f"mode={oct(mode)}",
                            risk="SUID/SGID bit set — privilege escalation risk",
                            fix="Remove SUID/SGID bits: chmod u-s,g-s <file>",
                        )
                    )
            except OSError:
                pass


def scan_skill(skill_path: Path) -> AuditReport:
    """Run full security audit on a skill directory."""
    report = AuditReport(
        skill_name=skill_path.name,
        skill_path=str(skill_path),
    )

    # Check SKILL.md exists
    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        report.findings.append(
            Finding(
                severity=Severity.HIGH,
                category="STRUCTURE",
                file="SKILL.md",
                line=0,
                pattern="SKILL.md not found",
                risk="Missing SKILL.md — not a valid skill directory",
                fix="Ensure the path points to a valid skill directory with SKILL.md",
            )
        )

    # 1. Filesystem scan
    scan_filesystem(skill_path, report)

    # 2. Code scanning
    for code_file in skill_path.rglob("*"):
        if ".git" in code_file.parts:
            continue
        if code_file.is_file() and code_file.suffix.lower() in CODE_EXTENSIONS:
            report.scripts_scanned += 1
            scan_file_code(code_file, report)

    # 3. Prompt injection scanning
    for md_file in skill_path.rglob("*"):
        if ".git" in md_file.parts:
            continue
        if md_file.is_file() and md_file.suffix.lower() in MD_EXTENSIONS:
            report.md_files_scanned += 1
            scan_file_prompt_injection(md_file, report)

    # 4. Dependency scanning
    scan_dependencies(skill_path, report)

    return report


def clone_repo(url: str, skill_name: Optional[str] = None, cleanup: bool = False):
    """Clone a git repo to a temp directory and return the skill path."""
    tmp_dir = tempfile.mkdtemp(prefix="skill-audit-")
    try:
        subprocess.run(
            ["git", "clone", "--depth", "1", url, tmp_dir],
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"Error cloning {url}: {e.stderr}", file=sys.stderr)
        shutil.rmtree(tmp_dir, ignore_errors=True)  # noqa: SEC-AUDITOR
        sys.exit(1)

    if skill_name:
        skill_path = Path(tmp_dir) / skill_name
        if not skill_path.exists():
            # Try finding it
            matches = list(Path(tmp_dir).rglob(skill_name))
            if matches:
                skill_path = matches[0]
            else:
                print(f"Skill '{skill_name}' not found in repo", file=sys.stderr)
                shutil.rmtree(tmp_dir, ignore_errors=True)  # noqa: SEC-AUDITOR
                sys.exit(1)
    else:
        skill_path = Path(tmp_dir)

    return skill_path, tmp_dir if cleanup else None


def print_report(report: AuditReport):
    """Print formatted audit report to stdout."""
    verdict_symbols = {"PASS": "✅", "WARN": "⚠️", "FAIL": "❌"}
    v = report.verdict
    sym = verdict_symbols[v]

    print()
    print("╔" + "═" * 54 + "╗")
    print(f"║  SKILL SECURITY AUDIT REPORT{' ' * 25}║")
    print(f"║  Skill: {report.skill_name:<44} ║")
    print(f"║  Verdict: {sym} {v:<42}║")
    print("╠" + "═" * 54 + "╣")
    print(
        f"║  🔴 CRITICAL: {report.critical_count:<3} "
        f"🟡 HIGH: {report.high_count:<3} "
        f"⚪ INFO: {report.info_count:<3}{' ' * 10}║"
    )
    print(
        f"║  Files: {report.files_scanned}  "
        f"Scripts: {report.scripts_scanned}  "
        f"Markdown: {report.md_files_scanned}{' ' * (17 - len(str(report.files_scanned)) - len(str(report.scripts_scanned)) - len(str(report.md_files_scanned)))}║"
    )
    print("╚" + "═" * 54 + "╝")

    if not report.findings:
        print("\n  No security issues found. Skill is safe to install.\n")
        return

    print()

    # Sort by severity (critical first)
    sorted_findings = sorted(report.findings, key=lambda f: -f.severity)

    for f in sorted_findings:
        label = SEVERITY_LABELS[f.severity]
        loc = f"{f.file}:{f.line}" if f.line > 0 else f.file
        print(f"{label} [{f.category}] {loc}")
        print(f"   Pattern: {f.pattern}")
        print(f"   Risk: {f.risk}")
        print(f"   Fix: {f.fix}")
        print()


def main():
    parser = argparse.ArgumentParser(
        description="Skill Security Auditor — Scan skills for security risks before installation"
    )
    parser.add_argument(
        "path",
        help="Path to skill directory or git repo URL",
    )
    parser.add_argument(
        "--skill",
        help="Skill name within a git repo (subdirectory)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Strict mode — any WARN becomes FAIL",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        help="Output JSON report instead of formatted text",
    )
    parser.add_argument(
        "--cleanup",
        action="store_true",
        help="Remove cloned repo after audit (only for git URLs)",
    )

    args = parser.parse_args()

    cleanup_dir = None

    # Handle git URLs
    if args.path.startswith(("http://", "https://", "git@")):
        skill_path, cleanup_dir = clone_repo(args.path, args.skill, cleanup=True)
    else:
        skill_path = Path(args.path).resolve()
        if not skill_path.exists():
            print(f"Error: path does not exist: {skill_path}", file=sys.stderr)
            sys.exit(1)
        if not skill_path.is_dir():
            print(f"Error: path is not a directory: {skill_path}", file=sys.stderr)
            sys.exit(1)

    try:
        report = scan_skill(skill_path)

        if args.json_output:
            print(json.dumps(report.to_dict(), indent=2))
        else:
            print_report(report)

        # Exit code
        if args.strict and report.verdict == "WARN":
            sys.exit(1)
        elif report.verdict == "FAIL":
            sys.exit(1)
        elif report.verdict == "WARN":
            sys.exit(2)
        else:
            sys.exit(0)

    finally:
        if cleanup_dir:
            shutil.rmtree(cleanup_dir, ignore_errors=True)  # noqa: SEC-AUDITOR


if __name__ == "__main__":
    main()
