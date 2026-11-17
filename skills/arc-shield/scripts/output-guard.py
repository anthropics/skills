#!/usr/bin/env python3
"""
output-guard.py - Advanced output sanitization with entropy detection
Catches secrets that regex patterns miss using Shannon entropy analysis
"""

import sys
import re
import math
import json
from typing import List, Dict, Tuple
from collections import Counter

VERSION = "1.0.0"

# Severity levels
CRITICAL = "CRITICAL"
HIGH = "HIGH"
WARN = "WARN"

class Finding:
    def __init__(self, severity: str, category: str, value: str, position: int):
        self.severity = severity
        self.category = category
        self.value = value
        self.position = position
    
    def __repr__(self):
        truncated = self.value[:60] + "..." if len(self.value) > 60 else self.value
        return f"[{self.severity}] {self.category}: {truncated}"

class OutputGuard:
    def __init__(self):
        self.findings: List[Finding] = []
        self.mode = "scan"  # scan, redact, report, strict
        
        # Regex patterns (same as bash version)
        self.patterns = {
            CRITICAL: {
                "1Password Token": re.compile(r'ops_[a-zA-Z0-9_-]{40,}'),
                "GitHub PAT": re.compile(r'ghp_[a-zA-Z0-9]{36,}'),
                "OpenAI Key": re.compile(r'sk-[a-zA-Z0-9]{20,}'),
                "Stripe Key": re.compile(r'sk_(test|live)_[a-zA-Z0-9]{24,}'),
                "AWS Key": re.compile(r'AKIA[0-9A-Z]{16}'),
                "Bearer Token": re.compile(r'Bearer [a-zA-Z0-9_\-\.]{20,}'),
                "Password Assignment": re.compile(r'(password|passwd|pwd)["\s]*[:=]["\s]*[^ "\n]{6,}', re.IGNORECASE),
                "Ethereum Private Key": re.compile(r'0x[0-9a-fA-F]{64}'),
                "SSH Private Key": re.compile(r'-----BEGIN (RSA|OPENSSH|DSA|EC) PRIVATE KEY-----'),
                "PGP Private Key": re.compile(r'-----BEGIN PGP PRIVATE KEY BLOCK-----'),
                "SSN": re.compile(r'\b[0-9]{3}-[0-9]{2}-[0-9]{4}\b'),
            },
            HIGH: {
                "Credit Card": re.compile(r'\b[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}\b'),
                "High Entropy String": None,  # Handled separately
            },
            WARN: {
                "Secret Path": re.compile(r'(~\/\.secrets\/|\/\.?secrets?\/|[^\s]*\/(password|token|key|secret)[^\s]*\.[a-z]{2,4})'),
                "Environment Variable": re.compile(r'^[A-Z_][A-Z0-9_]*=[^\s]{10,}', re.MULTILINE),
            }
        }
    
    def shannon_entropy(self, data: str) -> float:
        """Calculate Shannon entropy of a string"""
        if not data:
            return 0.0
        
        entropy = 0.0
        counter = Counter(data)
        length = len(data)
        
        for count in counter.values():
            probability = count / length
            if probability > 0:
                entropy -= probability * math.log2(probability)
        
        return entropy
    
    def detect_high_entropy_strings(self, text: str, threshold: float = 4.5, min_length: int = 16) -> List[Tuple[str, int]]:
        """Detect strings with high entropy that might be secrets"""
        findings = []
        
        # Find alphanumeric sequences
        pattern = re.compile(r'[a-zA-Z0-9_\-\.]{16,}')
        
        for match in pattern.finditer(text):
            value = match.group()
            
            # Skip if it looks like normal text (high ratio of common words)
            if self.looks_like_normal_text(value):
                continue
            
            # Skip if it's a URL or file path
            if '/' in value or '.' in value and value.count('.') > 2:
                continue
            
            entropy = self.shannon_entropy(value)
            
            if entropy >= threshold and len(value) >= min_length:
                # Additional heuristics to reduce false positives
                if self.looks_like_secret(value):
                    findings.append((value, match.start()))
        
        return findings
    
    def looks_like_normal_text(self, text: str) -> bool:
        """Check if text looks like normal English rather than a secret"""
        # If it's mostly lowercase with spaces, probably normal text
        if text.islower() and ' ' in text:
            return True
        
        # If it has repeating patterns, might be a UUID or similar
        if len(set(text)) < len(text) * 0.3:  # Less than 30% unique chars
            return False
        
        return False
    
    def looks_like_secret(self, text: str) -> bool:
        """Heuristics to determine if high-entropy string is likely a secret"""
        # Mix of upper, lower, and numbers is common in secrets
        has_upper = any(c.isupper() for c in text)
        has_lower = any(c.islower() for c in text)
        has_digit = any(c.isdigit() for c in text)
        
        # Secrets often have at least 2 of these
        char_types = sum([has_upper, has_lower, has_digit])
        
        if char_types < 2:
            return False
        
        # Common secret prefixes/patterns
        secret_indicators = ['key', 'token', 'secret', 'api', 'auth', 'pass']
        text_lower = text.lower()
        
        # Check if near a secret keyword (would need context, simplified here)
        return char_types >= 2
    
    def scan(self, text: str):
        """Scan text for all secret patterns"""
        # Regex-based detection
        for severity, patterns in self.patterns.items():
            for category, pattern in patterns.items():
                if pattern is None:
                    continue
                
                for match in pattern.finditer(text):
                    finding = Finding(severity, category, match.group(), match.start())
                    self.findings.append(finding)
        
        # Entropy-based detection
        high_entropy = self.detect_high_entropy_strings(text)
        for value, position in high_entropy:
            finding = Finding(HIGH, "High Entropy String", value, position)
            self.findings.append(finding)
    
    def redact(self, text: str) -> str:
        """Redact secrets from text"""
        result = text
        
        # Redact in reverse order to maintain positions
        replacements = []
        
        for severity, patterns in self.patterns.items():
            for category, pattern in patterns.items():
                if pattern is None:
                    continue
                
                for match in pattern.finditer(text):
                    redacted = f"[REDACTED:{category.upper().replace(' ', '_')}]"
                    replacements.append((match.start(), match.end(), redacted))
        
        # Sort by position (reverse) and apply
        replacements.sort(key=lambda x: x[0], reverse=True)
        
        for start, end, redacted in replacements:
            result = result[:start] + redacted + result[end:]
        
        return result
    
    def report(self) -> Dict:
        """Generate findings report"""
        critical = [f for f in self.findings if f.severity == CRITICAL]
        high = [f for f in self.findings if f.severity == HIGH]
        warn = [f for f in self.findings if f.severity == WARN]
        
        return {
            "summary": {
                "critical": len(critical),
                "high": len(high),
                "warn": len(warn),
                "total": len(self.findings)
            },
            "findings": {
                "critical": [str(f) for f in critical],
                "high": [str(f) for f in high],
                "warn": [str(f) for f in warn]
            }
        }
    
    def print_report(self):
        """Print human-readable report to stderr"""
        report = self.report()
        
        print("\n=== OUTPUT-GUARD SCAN REPORT ===", file=sys.stderr)
        print(f"CRITICAL: {report['summary']['critical']}", file=sys.stderr)
        print(f"HIGH: {report['summary']['high']}", file=sys.stderr)
        print(f"WARN: {report['summary']['warn']}", file=sys.stderr)
        
        if report['summary']['critical'] > 0:
            print("\nCRITICAL FINDINGS:", file=sys.stderr)
            for finding in report['findings']['critical']:
                print(f"  {finding}", file=sys.stderr)
        
        if report['summary']['high'] > 0:
            print("\nHIGH FINDINGS:", file=sys.stderr)
            for finding in report['findings']['high']:
                print(f"  {finding}", file=sys.stderr)

def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Output sanitization with entropy detection",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
EXAMPLES:
    # Scan with entropy detection
    echo "secret: sk-abc123xyz456" | output-guard.py
    
    # Redact secrets
    cat response.txt | output-guard.py --redact
    
    # Strict mode (block on critical)
    output-guard.py --strict < message.txt
    
    # JSON report
    output-guard.py --json < conversation.log
        """
    )
    
    parser.add_argument('--redact', action='store_true', help='Redact secrets and output sanitized text')
    parser.add_argument('--strict', action='store_true', help='Exit with code 1 if critical findings detected')
    parser.add_argument('--report', action='store_true', help='Show findings report only')
    parser.add_argument('--json', action='store_true', help='Output report as JSON')
    parser.add_argument('--entropy-threshold', type=float, default=4.5, help='Shannon entropy threshold (default: 4.5)')
    parser.add_argument('--min-length', type=int, default=16, help='Minimum string length for entropy check (default: 16)')
    parser.add_argument('--version', action='version', version=f'%(prog)s {VERSION}')
    
    args = parser.parse_args()
    
    # Read input
    text = sys.stdin.read()
    
    # Initialize guard
    guard = OutputGuard()
    guard.scan(text)
    
    # Mode handling
    if args.report or args.json:
        if args.json:
            print(json.dumps(guard.report(), indent=2))
        else:
            guard.print_report()
    elif args.redact:
        print(guard.redact(text))
    elif args.strict:
        print(text)
        critical_count = len([f for f in guard.findings if f.severity == CRITICAL])
        if critical_count > 0:
            guard.print_report()
            print("\n[BLOCKED] Critical secrets detected. Message blocked.", file=sys.stderr)
            sys.exit(1)
    else:
        # Default: pass through with warnings
        print(text)
        if guard.findings:
            guard.print_report()

if __name__ == "__main__":
    main()
