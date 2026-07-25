#!/usr/bin/env python3
"""
Threat Modeler

Performs STRIDE threat analysis on system components.
Generates threat model documentation with risk scores.

Usage:
    python threat_modeler.py --component "User Authentication"
    python threat_modeler.py --component "API Gateway" --assets "user_data,sessions"
    python threat_modeler.py --interactive
    python threat_modeler.py --list-threats
"""

import argparse
import json
import sys
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict
from enum import Enum


class STRIDECategory(Enum):
    SPOOFING = "Spoofing"
    TAMPERING = "Tampering"
    REPUDIATION = "Repudiation"
    INFORMATION_DISCLOSURE = "Information Disclosure"
    DENIAL_OF_SERVICE = "Denial of Service"
    ELEVATION_OF_PRIVILEGE = "Elevation of Privilege"


@dataclass
class Threat:
    category: str
    name: str
    description: str
    attack_vector: str
    impact: str
    likelihood: int  # 1-5
    severity: int    # 1-5
    mitigations: List[str]

    @property
    def risk_score(self) -> int:
        return self.likelihood * self.severity

    @property
    def risk_level(self) -> str:
        score = self.risk_score
        if score >= 20:
            return "Critical"
        elif score >= 12:
            return "High"
        elif score >= 6:
            return "Medium"
        else:
            return "Low"


# Comprehensive threat database
THREAT_DATABASE = {
    "authentication": [
        Threat(
            category="Spoofing",
            name="Credential Theft",
            description="Attacker obtains valid credentials through phishing or theft",
            attack_vector="Phishing emails, keyloggers, credential stuffing",
            impact="Full account compromise, data access",
            likelihood=4,
            severity=5,
            mitigations=[
                "Implement multi-factor authentication (MFA)",
                "Use phishing-resistant authentication (FIDO2/WebAuthn)",
                "Deploy credential monitoring and breach detection",
                "Enforce strong password policies with complexity requirements"
            ]
        ),
        Threat(
            category="Spoofing",
            name="Session Hijacking",
            description="Attacker steals or predicts session tokens",
            attack_vector="XSS, network sniffing, session fixation",
            impact="Unauthorized access to user session",
            likelihood=3,
            severity=4,
            mitigations=[
                "Use secure, HttpOnly, SameSite cookies",
                "Implement session binding (IP, user agent)",
                "Rotate session tokens after authentication",
                "Use short session timeouts for sensitive operations"
            ]
        ),
        Threat(
            category="Tampering",
            name="JWT Token Manipulation",
            description="Attacker modifies JWT claims or signature",
            attack_vector="Algorithm confusion, weak secrets, none algorithm",
            impact="Privilege escalation, identity spoofing",
            likelihood=3,
            severity=5,
            mitigations=[
                "Use asymmetric algorithms (RS256, ES256)",
                "Validate algorithm in code, not from token",
                "Implement proper key management",
                "Add expiration and audience validation"
            ]
        ),
        Threat(
            category="Repudiation",
            name="Authentication Event Denial",
            description="User denies performing authentication actions",
            attack_vector="Claim of compromised credentials",
            impact="Dispute resolution difficulty, fraud",
            likelihood=2,
            severity=3,
            mitigations=[
                "Log all authentication events with timestamps",
                "Capture device fingerprints and IP addresses",
                "Implement tamper-evident audit logs",
                "Use digital signatures for critical actions"
            ]
        ),
        Threat(
            category="Information Disclosure",
            name="Password Hash Exposure",
            description="Password hashes leaked through breach or injection",
            attack_vector="SQL injection, backup exposure, insider threat",
            impact="Mass credential compromise",
            likelihood=2,
            severity=5,
            mitigations=[
                "Use strong password hashing (Argon2id, bcrypt)",
                "Implement database encryption at rest",
                "Apply parameterized queries everywhere",
                "Segment database access by function"
            ]
        ),
        Threat(
            category="Denial of Service",
            name="Authentication Brute Force",
            description="Attacker overwhelms authentication service",
            attack_vector="Distributed credential stuffing, password spraying",
            impact="Service unavailability, account lockouts",
            likelihood=4,
            severity=3,
            mitigations=[
                "Implement progressive rate limiting",
                "Use CAPTCHA after failed attempts",
                "Deploy account lockout with notification",
                "Use distributed denial of service protection"
            ]
        ),
        Threat(
            category="Elevation of Privilege",
            name="Privilege Escalation via Auth Bypass",
            description="Attacker gains admin access through auth flaws",
            attack_vector="IDOR, insecure direct object references, role confusion",
            impact="Full system compromise",
            likelihood=2,
            severity=5,
            mitigations=[
                "Implement server-side authorization checks",
                "Use role-based access control (RBAC)",
                "Validate permissions on every request",
                "Audit privilege changes"
            ]
        )
    ],
    "api": [
        Threat(
            category="Spoofing",
            name="API Key Impersonation",
            description="Attacker uses stolen or leaked API keys",
            attack_vector="GitHub exposure, client-side storage, logging",
            impact="Unauthorized API access, data theft",
            likelihood=4,
            severity=4,
            mitigations=[
                "Implement API key rotation policies",
                "Use short-lived tokens where possible",
                "Monitor for exposed secrets in repositories",
                "Implement IP allowlisting for API keys"
            ]
        ),
        Threat(
            category="Tampering",
            name="Request Manipulation",
            description="Attacker modifies API requests in transit",
            attack_vector="Man-in-the-middle, proxy interception",
            impact="Data corruption, unauthorized actions",
            likelihood=2,
            severity=4,
            mitigations=[
                "Enforce TLS 1.3 for all connections",
                "Implement request signing (HMAC)",
                "Use certificate pinning for mobile apps",
                "Validate request integrity on server"
            ]
        ),
        Threat(
            category="Information Disclosure",
            name="Excessive Data Exposure",
            description="API returns more data than needed",
            attack_vector="Response inspection, schema analysis",
            impact="Sensitive data leakage",
            likelihood=4,
            severity=3,
            mitigations=[
                "Implement field-level access control",
                "Use GraphQL with depth limiting",
                "Apply response filtering based on role",
                "Audit API responses for sensitive fields"
            ]
        ),
        Threat(
            category="Denial of Service",
            name="API Rate Limit Bypass",
            description="Attacker circumvents rate limiting",
            attack_vector="Distributed requests, header spoofing",
            impact="Service degradation, resource exhaustion",
            likelihood=3,
            severity=3,
            mitigations=[
                "Implement layered rate limiting",
                "Use token bucket or leaky bucket algorithms",
                "Rate limit by user, IP, and API key",
                "Deploy API gateway with DoS protection"
            ]
        )
    ],
    "database": [
        Threat(
            category="Tampering",
            name="SQL Injection",
            description="Attacker injects malicious SQL commands",
            attack_vector="Input fields, URL parameters, headers",
            impact="Data theft, modification, destruction",
            likelihood=3,
            severity=5,
            mitigations=[
                "Use parameterized queries exclusively",
                "Apply input validation and sanitization",
                "Implement least privilege database accounts",
                "Deploy web application firewall (WAF)"
            ]
        ),
        Threat(
            category="Information Disclosure",
            name="Unencrypted Data at Rest",
            description="Sensitive data stored without encryption",
            attack_vector="Physical theft, backup exposure, insider threat",
            impact="Mass data breach",
            likelihood=2,
            severity=5,
            mitigations=[
                "Implement transparent data encryption (TDE)",
                "Use field-level encryption for PII",
                "Encrypt database backups",
                "Manage encryption keys securely"
            ]
        ),
        Threat(
            category="Repudiation",
            name="Audit Log Tampering",
            description="Attacker modifies or deletes database logs",
            attack_vector="SQL injection, admin access, log rotation",
            impact="Cannot prove what actions occurred",
            likelihood=2,
            severity=4,
            mitigations=[
                "Write audit logs to immutable storage",
                "Implement cryptographic log chaining",
                "Use separate audit database with restricted access",
                "Monitor for log gaps and anomalies"
            ]
        )
    ],
    "network": [
        Threat(
            category="Information Disclosure",
            name="Network Traffic Interception",
            description="Attacker captures unencrypted traffic",
            attack_vector="ARP spoofing, rogue access points, packet sniffing",
            impact="Credential theft, data exposure",
            likelihood=2,
            severity=4,
            mitigations=[
                "Enforce TLS everywhere (no HTTP)",
                "Implement HSTS with preloading",
                "Use mutual TLS for service-to-service",
                "Deploy network segmentation"
            ]
        ),
        Threat(
            category="Denial of Service",
            name="DDoS Attack",
            description="Attacker floods network with traffic",
            attack_vector="Volumetric attacks, application layer attacks",
            impact="Complete service unavailability",
            likelihood=3,
            severity=4,
            mitigations=[
                "Deploy CDN with DDoS protection",
                "Implement rate limiting at edge",
                "Use anycast DNS distribution",
                "Have incident response runbook ready"
            ]
        )
    ],
    "storage": [
        Threat(
            category="Information Disclosure",
            name="Insecure File Upload",
            description="Attacker accesses uploaded files",
            attack_vector="Direct URL access, path traversal",
            impact="Data breach, malware distribution",
            likelihood=3,
            severity=4,
            mitigations=[
                "Generate random file names",
                "Store files outside web root",
                "Implement signed URLs with expiration",
                "Scan uploads for malware"
            ]
        ),
        Threat(
            category="Tampering",
            name="File Integrity Violation",
            description="Attacker modifies stored files",
            attack_vector="Write access exploit, supply chain attack",
            impact="Data corruption, code execution",
            likelihood=2,
            severity=4,
            mitigations=[
                "Implement file integrity monitoring",
                "Use cryptographic hashes for verification",
                "Apply immutable storage for critical files",
                "Version control with audit trail"
            ]
        )
    ]
}

# Component to threat category mapping
COMPONENT_MAPPING = {
    "authentication": ["authentication"],
    "login": ["authentication"],
    "auth": ["authentication"],
    "api": ["api"],
    "api gateway": ["api", "network"],
    "rest api": ["api"],
    "graphql": ["api"],
    "database": ["database"],
    "db": ["database"],
    "postgres": ["database"],
    "mysql": ["database"],
    "mongodb": ["database"],
    "network": ["network"],
    "load balancer": ["network"],
    "cdn": ["network"],
    "storage": ["storage"],
    "s3": ["storage"],
    "file upload": ["storage"],
    "user service": ["authentication", "database"],
    "payment": ["api", "database", "authentication"],
    "web application": ["authentication", "api", "database", "network"],
    "microservice": ["api", "network", "authentication"],
}


def get_threats_for_component(component: str) -> List[Threat]:
    """Get applicable threats for a component."""
    component_lower = component.lower()

    # Find matching categories
    categories = []
    for key, value in COMPONENT_MAPPING.items():
        if key in component_lower:
            categories.extend(value)

    # If no specific match, return all threats
    if not categories:
        categories = list(THREAT_DATABASE.keys())

    # Collect unique threats
    threats = []
    seen = set()
    for category in set(categories):
        if category in THREAT_DATABASE:
            for threat in THREAT_DATABASE[category]:
                threat_key = (threat.category, threat.name)
                if threat_key not in seen:
                    threats.append(threat)
                    seen.add(threat_key)

    return sorted(threats, key=lambda t: t.risk_score, reverse=True)


def calculate_dread_score(threat: Threat) -> Dict:
    """Calculate DREAD score for a threat."""
    # Map threat properties to DREAD factors
    damage = threat.severity * 2
    reproducibility = 8 if threat.likelihood >= 4 else (5 if threat.likelihood >= 2 else 3)
    exploitability = threat.likelihood * 2
    affected_users = 8 if "mass" in threat.impact.lower() or "full" in threat.impact.lower() else 5
    discoverability = 7 if threat.likelihood >= 3 else 4

    dread = {
        "damage": min(damage, 10),
        "reproducibility": reproducibility,
        "exploitability": min(exploitability, 10),
        "affected_users": affected_users,
        "discoverability": discoverability
    }
    dread["total"] = sum(dread.values()) / 5
    return dread


def format_threat_report(component: str, threats: List[Threat]) -> str:
    """Format threats as a readable report."""
    lines = []
    lines.append("=" * 70)
    lines.append(f"THREAT MODEL: {component.upper()}")
    lines.append("=" * 70)
    lines.append("")

    # Summary
    critical = sum(1 for t in threats if t.risk_level == "Critical")
    high = sum(1 for t in threats if t.risk_level == "High")
    medium = sum(1 for t in threats if t.risk_level == "Medium")
    low = sum(1 for t in threats if t.risk_level == "Low")

    lines.append("SUMMARY:")
    lines.append(f"  Total Threats: {len(threats)}")
    lines.append(f"  Critical: {critical} | High: {high} | Medium: {medium} | Low: {low}")
    lines.append("")

    # Threats by STRIDE category
    for stride in STRIDECategory:
        category_threats = [t for t in threats if t.category == stride.value]
        if category_threats:
            lines.append("-" * 70)
            lines.append(f"[{stride.value.upper()}]")
            lines.append("-" * 70)

            for threat in category_threats:
                dread = calculate_dread_score(threat)
                lines.append("")
                lines.append(f"  {threat.name}")
                lines.append(f"  Risk: {threat.risk_level} (Score: {threat.risk_score}/25)")
                lines.append(f"  DREAD: {dread['total']:.1f}/10")
                lines.append(f"  Description: {threat.description}")
                lines.append(f"  Attack Vector: {threat.attack_vector}")
                lines.append(f"  Impact: {threat.impact}")
                lines.append("  Mitigations:")
                for m in threat.mitigations:
                    lines.append(f"    - {m}")

    lines.append("")
    lines.append("=" * 70)
    return "\n".join(lines)


def format_json_report(component: str, threats: List[Threat]) -> Dict:
    """Format threats as JSON structure."""
    return {
        "component": component,
        "analysis_date": __import__('datetime').datetime.now().isoformat(),
        "summary": {
            "total_threats": len(threats),
            "by_risk_level": {
                "critical": sum(1 for t in threats if t.risk_level == "Critical"),
                "high": sum(1 for t in threats if t.risk_level == "High"),
                "medium": sum(1 for t in threats if t.risk_level == "Medium"),
                "low": sum(1 for t in threats if t.risk_level == "Low")
            }
        },
        "threats": [
            {
                "category": t.category,
                "name": t.name,
                "description": t.description,
                "attack_vector": t.attack_vector,
                "impact": t.impact,
                "likelihood": t.likelihood,
                "severity": t.severity,
                "risk_score": t.risk_score,
                "risk_level": t.risk_level,
                "dread": calculate_dread_score(t),
                "mitigations": t.mitigations
            }
            for t in threats
        ]
    }


def interactive_mode():
    """Run interactive threat modeling session."""
    print("\n" + "=" * 50)
    print("STRIDE THREAT MODELER - Interactive Mode")
    print("=" * 50)

    component = input("\nEnter component name (e.g., 'User Authentication'): ").strip()
    if not component:
        print("Component name required.")
        return

    threats = get_threats_for_component(component)

    if not threats:
        print(f"No threats found for component: {component}")
        return

    print(format_threat_report(component, threats))


def list_all_threats():
    """List all threats in the database."""
    print("\n" + "=" * 50)
    print("THREAT DATABASE")
    print("=" * 50)

    for category, threats in THREAT_DATABASE.items():
        print(f"\n[{category.upper()}]")
        for threat in threats:
            print(f"  - {threat.category}: {threat.name} (Risk: {threat.risk_level})")


def main():
    parser = argparse.ArgumentParser(
        description="STRIDE Threat Modeler - Analyze security threats",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze authentication component
  python threat_modeler.py --component "User Authentication"

  # Analyze with specific assets
  python threat_modeler.py --component "API Gateway" --assets "user_data,tokens"

  # JSON output for integration
  python threat_modeler.py --component "Database" --json

  # Interactive mode
  python threat_modeler.py --interactive

  # List all threats in database
  python threat_modeler.py --list-threats
        """
    )

    parser.add_argument(
        "--component", "-c",
        help="Component to analyze (e.g., 'User Authentication', 'API Gateway')"
    )
    parser.add_argument(
        "--assets", "-a",
        help="Comma-separated list of assets to protect"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output as JSON"
    )
    parser.add_argument(
        "--interactive", "-i",
        action="store_true",
        help="Run in interactive mode"
    )
    parser.add_argument(
        "--list-threats", "-l",
        action="store_true",
        help="List all threats in database"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path"
    )

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.list_threats:
        list_all_threats()
        return

    if not args.component:
        parser.error("--component is required (or use --interactive)")

    threats = get_threats_for_component(args.component)

    if args.json:
        output = json.dumps(format_json_report(args.component, threats), indent=2)
    else:
        output = format_threat_report(args.component, threats)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        print(f"Report written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
