#!/usr/bin/env python3
"""
Compliance Checker - Verify security compliance against SOC 2, PCI-DSS, HIPAA, GDPR.

Table of Contents:
    ComplianceChecker - Main class for compliance verification
        __init__         - Initialize with target path and framework
        check()          - Run compliance checks for selected framework
        check_soc2()     - Check SOC 2 Type II controls
        check_pci_dss()  - Check PCI-DSS v4.0 requirements
        check_hipaa()    - Check HIPAA security rule requirements
        check_gdpr()     - Check GDPR data protection requirements
        _check_encryption_at_rest() - Verify data encryption
        _check_access_controls() - Verify access control implementation
        _check_logging()  - Verify audit logging
        _check_secrets_management() - Verify secrets handling
        _calculate_compliance_score() - Calculate overall compliance score
    main() - CLI entry point

Usage:
    python compliance_checker.py /path/to/project
    python compliance_checker.py /path/to/project --framework soc2
    python compliance_checker.py /path/to/project --framework pci-dss --output report.json
"""

import os
import sys
import json
import re
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class ComplianceControl:
    """Represents a compliance control check result."""
    control_id: str
    framework: str
    category: str
    title: str
    description: str
    status: str  # passed, failed, warning, not_applicable
    evidence: List[str]
    recommendation: str
    severity: str  # critical, high, medium, low


class ComplianceChecker:
    """Verify security compliance against industry frameworks."""

    FRAMEWORKS = ['soc2', 'pci-dss', 'hipaa', 'gdpr', 'all']

    def __init__(
        self,
        target_path: str,
        framework: str = "all",
        verbose: bool = False
    ):
        """
        Initialize the compliance checker.

        Args:
            target_path: Directory to scan
            framework: Compliance framework to check (soc2, pci-dss, hipaa, gdpr, all)
            verbose: Enable verbose output
        """
        self.target_path = Path(target_path)
        self.framework = framework.lower()
        self.verbose = verbose
        self.controls: List[ComplianceControl] = []
        self.files_scanned = 0

    def check(self) -> Dict:
        """
        Run compliance checks for selected framework.

        Returns:
            Dict with compliance results
        """
        print(f"Compliance Checker - Scanning: {self.target_path}")
        print(f"Framework: {self.framework.upper()}")
        print()

        if not self.target_path.exists():
            return {"status": "error", "message": f"Path not found: {self.target_path}"}

        start_time = datetime.now()

        # Run framework-specific checks
        if self.framework in ('soc2', 'all'):
            self.check_soc2()
        if self.framework in ('pci-dss', 'all'):
            self.check_pci_dss()
        if self.framework in ('hipaa', 'all'):
            self.check_hipaa()
        if self.framework in ('gdpr', 'all'):
            self.check_gdpr()

        end_time = datetime.now()
        scan_duration = (end_time - start_time).total_seconds()

        # Calculate statistics
        passed = len([c for c in self.controls if c.status == 'passed'])
        failed = len([c for c in self.controls if c.status == 'failed'])
        warnings = len([c for c in self.controls if c.status == 'warning'])
        na = len([c for c in self.controls if c.status == 'not_applicable'])

        compliance_score = self._calculate_compliance_score()

        result = {
            "status": "completed",
            "target": str(self.target_path),
            "framework": self.framework,
            "scan_duration_seconds": round(scan_duration, 2),
            "compliance_score": compliance_score,
            "compliance_level": self._get_compliance_level(compliance_score),
            "summary": {
                "passed": passed,
                "failed": failed,
                "warnings": warnings,
                "not_applicable": na,
                "total": len(self.controls)
            },
            "controls": [asdict(c) for c in self.controls]
        }

        self._print_summary(result)

        return result

    def check_soc2(self):
        """Check SOC 2 Type II controls."""
        if self.verbose:
            print("  Checking SOC 2 Type II controls...")

        # CC1: Control Environment - Access Controls
        self._check_access_controls_soc2()

        # CC2: Communication and Information
        self._check_documentation()

        # CC3: Risk Assessment
        self._check_risk_assessment()

        # CC6: Logical and Physical Access Controls
        self._check_authentication()

        # CC7: System Operations
        self._check_logging()

        # CC8: Change Management
        self._check_change_management()

    def check_pci_dss(self):
        """Check PCI-DSS v4.0 requirements."""
        if self.verbose:
            print("  Checking PCI-DSS v4.0 requirements...")

        # Requirement 3: Protect stored cardholder data
        self._check_data_encryption()

        # Requirement 4: Encrypt transmission of cardholder data
        self._check_transmission_encryption()

        # Requirement 6: Develop and maintain secure systems
        self._check_secure_development()

        # Requirement 8: Identify users and authenticate access
        self._check_strong_authentication()

        # Requirement 10: Log and monitor all access
        self._check_audit_logging()

        # Requirement 11: Test security of systems regularly
        self._check_security_testing()

    def check_hipaa(self):
        """Check HIPAA security rule requirements."""
        if self.verbose:
            print("  Checking HIPAA Security Rule requirements...")

        # 164.312(a)(1): Access Control
        self._check_hipaa_access_control()

        # 164.312(b): Audit Controls
        self._check_hipaa_audit()

        # 164.312(c)(1): Integrity Controls
        self._check_hipaa_integrity()

        # 164.312(d): Person or Entity Authentication
        self._check_hipaa_authentication()

        # 164.312(e)(1): Transmission Security
        self._check_hipaa_transmission()

    def check_gdpr(self):
        """Check GDPR data protection requirements."""
        if self.verbose:
            print("  Checking GDPR requirements...")

        # Article 25: Data protection by design
        self._check_privacy_by_design()

        # Article 32: Security of processing
        self._check_gdpr_security()

        # Article 33/34: Breach notification
        self._check_breach_notification()

        # Article 17: Right to erasure
        self._check_data_deletion()

        # Article 20: Data portability
        self._check_data_export()

    def _check_access_controls_soc2(self):
        """SOC 2 CC1/CC6: Check access control implementation."""
        evidence = []
        status = 'failed'

        # Look for authentication middleware
        auth_patterns = [
            r'authMiddleware',
            r'requireAuth',
            r'isAuthenticated',
            r'@login_required',
            r'@authenticated',
            r'passport\.authenticate',
            r'jwt\.verify',
            r'verifyToken'
        ]

        for pattern in auth_patterns:
            files = self._search_files(pattern)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        # Check for RBAC implementation
        rbac_patterns = [r'role', r'permission', r'authorize', r'can\(', r'hasRole']
        for pattern in rbac_patterns:
            files = self._search_files(pattern)
            if files:
                evidence.extend(files[:2])
                if status == 'failed':
                    status = 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC6.1',
            framework='SOC 2',
            category='Logical Access Controls',
            title='Access Control Implementation',
            description='Verify authentication and authorization controls are implemented',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement authentication middleware and role-based access control (RBAC)',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_documentation(self):
        """SOC 2 CC2: Check security documentation."""
        evidence = []
        status = 'failed'

        doc_files = [
            'SECURITY.md',
            'docs/security.md',
            'CONTRIBUTING.md',
            'docs/security-policy.md',
            '.github/SECURITY.md'
        ]

        for doc in doc_files:
            doc_path = self.target_path / doc
            if doc_path.exists():
                evidence.append(str(doc))
                status = 'passed' if 'security' in doc.lower() else 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC2.1',
            framework='SOC 2',
            category='Communication and Information',
            title='Security Documentation',
            description='Verify security policies and procedures are documented',
            status=status,
            evidence=evidence,
            recommendation='Create SECURITY.md documenting security policies, incident response, and vulnerability reporting',
            severity='medium' if status == 'failed' else 'low'
        ))

    def _check_risk_assessment(self):
        """SOC 2 CC3: Check risk assessment artifacts."""
        evidence = []
        status = 'failed'

        # Look for security scanning configuration
        scan_configs = [
            '.snyk',
            '.github/workflows/security.yml',
            '.github/workflows/codeql.yml',
            'trivy.yaml',
            '.semgrep.yml',
            'sonar-project.properties'
        ]

        for config in scan_configs:
            config_path = self.target_path / config
            if config_path.exists():
                evidence.append(str(config))
                status = 'passed'
                break

        # Check for dependabot/renovate
        dep_configs = [
            '.github/dependabot.yml',
            'renovate.json',
            '.github/renovate.json'
        ]

        for config in dep_configs:
            config_path = self.target_path / config
            if config_path.exists():
                evidence.append(str(config))
                if status == 'failed':
                    status = 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC3.1',
            framework='SOC 2',
            category='Risk Assessment',
            title='Automated Security Scanning',
            description='Verify automated vulnerability scanning is configured',
            status=status,
            evidence=evidence,
            recommendation='Configure automated security scanning (Snyk, CodeQL, Trivy) and dependency updates (Dependabot)',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_authentication(self):
        """SOC 2 CC6: Check authentication strength."""
        evidence = []
        status = 'failed'

        # Check for MFA/2FA
        mfa_patterns = [r'mfa', r'2fa', r'totp', r'authenticator', r'twoFactor']
        for pattern in mfa_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:2])
                status = 'passed'
                break

        # Check for password hashing
        hash_patterns = [r'bcrypt', r'argon2', r'scrypt', r'pbkdf2']
        for pattern in hash_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:2])
                if status == 'failed':
                    status = 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC6.2',
            framework='SOC 2',
            category='Authentication',
            title='Strong Authentication',
            description='Verify multi-factor authentication and secure password storage',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement MFA/2FA and use bcrypt/argon2 for password hashing',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_logging(self):
        """SOC 2 CC7: Check audit logging implementation."""
        evidence = []
        status = 'failed'

        # Check for logging configuration
        log_patterns = [
            r'winston',
            r'pino',
            r'bunyan',
            r'logging\.getLogger',
            r'log\.info',
            r'logger\.',
            r'audit.*log'
        ]

        for pattern in log_patterns:
            files = self._search_files(pattern)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        # Check for structured logging
        struct_patterns = [r'json.*log', r'structured.*log', r'log.*format']
        for pattern in struct_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:2])
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC7.1',
            framework='SOC 2',
            category='System Operations',
            title='Audit Logging',
            description='Verify comprehensive audit logging is implemented',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement structured audit logging with security events (auth, access, changes)',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_change_management(self):
        """SOC 2 CC8: Check change management controls."""
        evidence = []
        status = 'failed'

        # Check for CI/CD configuration
        ci_configs = [
            '.github/workflows',
            '.gitlab-ci.yml',
            'Jenkinsfile',
            '.circleci/config.yml',
            'azure-pipelines.yml'
        ]

        for config in ci_configs:
            config_path = self.target_path / config
            if config_path.exists():
                evidence.append(str(config))
                status = 'passed'
                break

        # Check for branch protection indicators
        branch_patterns = [r'protected.*branch', r'require.*review', r'pull.*request']
        for pattern in branch_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:2])
                break

        self.controls.append(ComplianceControl(
            control_id='SOC2-CC8.1',
            framework='SOC 2',
            category='Change Management',
            title='CI/CD and Code Review',
            description='Verify automated deployment pipeline and code review process',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement CI/CD pipeline with required code reviews and branch protection',
            severity='medium' if status == 'failed' else 'low'
        ))

    def _check_data_encryption(self):
        """PCI-DSS Req 3: Check encryption at rest."""
        evidence = []
        status = 'failed'

        encryption_patterns = [
            r'AES',
            r'encrypt',
            r'crypto\.createCipher',
            r'Fernet',
            r'KMS',
            r'encryptedField'
        ]

        for pattern in encryption_patterns:
            files = self._search_files(pattern)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-3.5',
            framework='PCI-DSS',
            category='Protect Stored Data',
            title='Encryption at Rest',
            description='Verify sensitive data is encrypted at rest',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement AES-256 encryption for sensitive data storage using approved libraries',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_transmission_encryption(self):
        """PCI-DSS Req 4: Check encryption in transit."""
        evidence = []
        status = 'failed'

        tls_patterns = [
            r'https://',
            r'TLS',
            r'SSL',
            r'secure.*cookie',
            r'HSTS'
        ]

        for pattern in tls_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-4.1',
            framework='PCI-DSS',
            category='Encrypt Transmissions',
            title='TLS/HTTPS Enforcement',
            description='Verify TLS 1.2+ is enforced for all transmissions',
            status=status,
            evidence=evidence[:5],
            recommendation='Enforce HTTPS with TLS 1.2+, enable HSTS, use secure cookies',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_secure_development(self):
        """PCI-DSS Req 6: Check secure development practices."""
        evidence = []
        status = 'failed'

        # Check for input validation
        validation_patterns = [
            r'validator',
            r'sanitize',
            r'escape',
            r'zod',
            r'yup',
            r'joi'
        ]

        for pattern in validation_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-6.5',
            framework='PCI-DSS',
            category='Secure Development',
            title='Input Validation',
            description='Verify input validation and sanitization is implemented',
            status=status,
            evidence=evidence[:5],
            recommendation='Use validation libraries (Joi, Zod, validator.js) for all user input',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_strong_authentication(self):
        """PCI-DSS Req 8: Check authentication requirements."""
        evidence = []
        status = 'failed'

        # Check for session management
        session_patterns = [
            r'session.*timeout',
            r'maxAge',
            r'expiresIn',
            r'session.*expire'
        ]

        for pattern in session_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-8.6',
            framework='PCI-DSS',
            category='Authentication',
            title='Session Management',
            description='Verify session timeout and management controls',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement 15-minute session timeout, secure session tokens, and session invalidation on logout',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_audit_logging(self):
        """PCI-DSS Req 10: Check audit logging."""
        # Reuse SOC 2 logging check logic
        evidence = []
        status = 'failed'

        log_patterns = [r'audit', r'log.*event', r'security.*log']
        for pattern in log_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-10.2',
            framework='PCI-DSS',
            category='Logging and Monitoring',
            title='Security Event Logging',
            description='Verify security events are logged with sufficient detail',
            status=status,
            evidence=evidence[:5],
            recommendation='Log all authentication events, access to cardholder data, and administrative actions',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_security_testing(self):
        """PCI-DSS Req 11: Check security testing."""
        evidence = []
        status = 'failed'

        # Check for test configuration
        test_patterns = [
            r'security.*test',
            r'penetration.*test',
            r'vulnerability.*scan'
        ]

        for pattern in test_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        # Check for SAST/DAST configuration
        sast_configs = ['.snyk', '.semgrep.yml', 'sonar-project.properties']
        for config in sast_configs:
            if (self.target_path / config).exists():
                evidence.append(config)
                if status == 'failed':
                    status = 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='PCI-DSS-11.3',
            framework='PCI-DSS',
            category='Security Testing',
            title='Vulnerability Assessment',
            description='Verify regular security testing is performed',
            status=status,
            evidence=evidence[:5],
            recommendation='Configure SAST/DAST scanning and schedule quarterly penetration tests',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_hipaa_access_control(self):
        """HIPAA 164.312(a)(1): Access Control."""
        evidence = []
        status = 'failed'

        # Check for user identification
        auth_patterns = [r'user.*id', r'authentication', r'identity']
        for pattern in auth_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='HIPAA-164.312(a)(1)',
            framework='HIPAA',
            category='Access Control',
            title='Unique User Identification',
            description='Verify unique user identification for accessing PHI',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement unique user accounts with individual credentials for all PHI access',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_hipaa_audit(self):
        """HIPAA 164.312(b): Audit Controls."""
        evidence = []
        status = 'failed'

        audit_patterns = [r'audit.*trail', r'access.*log', r'phi.*log']
        for pattern in audit_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='HIPAA-164.312(b)',
            framework='HIPAA',
            category='Audit Controls',
            title='PHI Access Audit Trail',
            description='Verify audit trails for PHI access are maintained',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement comprehensive audit logging for all PHI access with who/what/when/where',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_hipaa_integrity(self):
        """HIPAA 164.312(c)(1): Integrity Controls."""
        evidence = []
        status = 'failed'

        integrity_patterns = [r'checksum', r'hash', r'signature', r'integrity']
        for pattern in integrity_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='HIPAA-164.312(c)(1)',
            framework='HIPAA',
            category='Integrity',
            title='Data Integrity Controls',
            description='Verify mechanisms to protect PHI from improper alteration',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement checksums, digital signatures, or hashing for PHI integrity verification',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_hipaa_authentication(self):
        """HIPAA 164.312(d): Authentication."""
        evidence = []
        status = 'failed'

        auth_patterns = [r'mfa', r'two.*factor', r'biometric', r'token.*auth']
        for pattern in auth_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='HIPAA-164.312(d)',
            framework='HIPAA',
            category='Authentication',
            title='Person Authentication',
            description='Verify mechanisms to authenticate person or entity accessing PHI',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement multi-factor authentication for all PHI access',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_hipaa_transmission(self):
        """HIPAA 164.312(e)(1): Transmission Security."""
        evidence = []
        status = 'failed'

        transmission_patterns = [r'tls', r'ssl', r'https', r'encrypt.*transit']
        for pattern in transmission_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='HIPAA-164.312(e)(1)',
            framework='HIPAA',
            category='Transmission Security',
            title='PHI Transmission Encryption',
            description='Verify PHI is encrypted during transmission',
            status=status,
            evidence=evidence[:5],
            recommendation='Enforce TLS 1.2+ for all PHI transmissions, implement end-to-end encryption',
            severity='critical' if status == 'failed' else 'low'
        ))

    def _check_privacy_by_design(self):
        """GDPR Article 25: Privacy by design."""
        evidence = []
        status = 'failed'

        privacy_patterns = [
            r'data.*minimization',
            r'privacy.*config',
            r'consent',
            r'gdpr'
        ]

        for pattern in privacy_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='GDPR-25',
            framework='GDPR',
            category='Privacy by Design',
            title='Data Minimization',
            description='Verify data collection is limited to necessary purposes',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement data minimization, purpose limitation, and privacy-by-default configurations',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_gdpr_security(self):
        """GDPR Article 32: Security of processing."""
        evidence = []
        status = 'failed'

        security_patterns = [r'encrypt', r'pseudonymization', r'anonymization']
        for pattern in security_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='GDPR-32',
            framework='GDPR',
            category='Security',
            title='Pseudonymization and Encryption',
            description='Verify appropriate security measures for personal data',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement encryption and pseudonymization for personal data processing',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_breach_notification(self):
        """GDPR Article 33/34: Breach notification."""
        evidence = []
        status = 'failed'

        breach_patterns = [
            r'breach.*notification',
            r'incident.*response',
            r'security.*incident'
        ]

        for pattern in breach_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        # Check for incident response documentation
        incident_docs = ['SECURITY.md', 'docs/incident-response.md', '.github/SECURITY.md']
        for doc in incident_docs:
            if (self.target_path / doc).exists():
                evidence.append(doc)
                if status == 'failed':
                    status = 'warning'
                break

        self.controls.append(ComplianceControl(
            control_id='GDPR-33',
            framework='GDPR',
            category='Breach Notification',
            title='Incident Response Procedure',
            description='Verify breach notification procedures are documented',
            status=status,
            evidence=evidence[:5],
            recommendation='Document incident response procedures with 72-hour notification capability',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_data_deletion(self):
        """GDPR Article 17: Right to erasure."""
        evidence = []
        status = 'failed'

        deletion_patterns = [
            r'delete.*user',
            r'erasure',
            r'right.*forgotten',
            r'data.*deletion',
            r'gdpr.*delete'
        ]

        for pattern in deletion_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='GDPR-17',
            framework='GDPR',
            category='Data Subject Rights',
            title='Right to Erasure',
            description='Verify data deletion capability is implemented',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement complete user data deletion including all backups and third-party systems',
            severity='high' if status == 'failed' else 'low'
        ))

    def _check_data_export(self):
        """GDPR Article 20: Data portability."""
        evidence = []
        status = 'failed'

        export_patterns = [
            r'export.*data',
            r'data.*portability',
            r'download.*data',
            r'gdpr.*export'
        ]

        for pattern in export_patterns:
            files = self._search_files(pattern, case_sensitive=False)
            if files:
                evidence.extend(files[:3])
                status = 'passed'
                break

        self.controls.append(ComplianceControl(
            control_id='GDPR-20',
            framework='GDPR',
            category='Data Subject Rights',
            title='Data Portability',
            description='Verify data export capability is implemented',
            status=status,
            evidence=evidence[:5],
            recommendation='Implement data export in machine-readable format (JSON, CSV)',
            severity='medium' if status == 'failed' else 'low'
        ))

    def _search_files(self, pattern: str, case_sensitive: bool = True) -> List[str]:
        """Search files for pattern matches."""
        matches = []
        flags = 0 if case_sensitive else re.IGNORECASE

        try:
            for root, dirs, files in os.walk(self.target_path):
                # Skip common non-relevant directories
                dirs[:] = [d for d in dirs if d not in {
                    'node_modules', '.git', '__pycache__', 'venv', '.venv',
                    'dist', 'build', 'coverage', '.next'
                }]

                for filename in files:
                    if filename.endswith(('.js', '.ts', '.py', '.go', '.java', '.md', '.yml', '.yaml', '.json')):
                        file_path = Path(root) / filename
                        try:
                            content = file_path.read_text(encoding='utf-8', errors='ignore')
                            if re.search(pattern, content, flags):
                                rel_path = str(file_path.relative_to(self.target_path))
                                matches.append(rel_path)
                                self.files_scanned += 1
                        except Exception:
                            pass
        except Exception:
            pass

        return matches[:10]  # Limit results

    def _calculate_compliance_score(self) -> float:
        """Calculate overall compliance score (0-100)."""
        if not self.controls:
            return 0.0

        # Weight by severity
        severity_weights = {'critical': 4.0, 'high': 3.0, 'medium': 2.0, 'low': 1.0}
        status_scores = {'passed': 1.0, 'warning': 0.5, 'failed': 0.0, 'not_applicable': None}

        total_weight = 0.0
        total_score = 0.0

        for control in self.controls:
            score = status_scores.get(control.status)
            if score is not None:  # Skip N/A
                weight = severity_weights.get(control.severity, 1.0)
                total_weight += weight
                total_score += score * weight

        return round((total_score / total_weight) * 100, 1) if total_weight > 0 else 0.0

    def _get_compliance_level(self, score: float) -> str:
        """Get compliance level from score."""
        if score >= 90:
            return "COMPLIANT"
        elif score >= 70:
            return "PARTIALLY_COMPLIANT"
        elif score >= 50:
            return "NON_COMPLIANT"
        return "CRITICAL_GAPS"

    def _print_summary(self, result: Dict):
        """Print compliance summary."""
        print("\n" + "=" * 60)
        print("COMPLIANCE CHECK SUMMARY")
        print("=" * 60)
        print(f"Target: {result['target']}")
        print(f"Framework: {result['framework'].upper()}")
        print(f"Scan duration: {result['scan_duration_seconds']}s")
        print(f"Compliance score: {result['compliance_score']}% ({result['compliance_level']})")
        print()

        summary = result['summary']
        print(f"Controls checked: {summary['total']}")
        print(f"  Passed:  {summary['passed']}")
        print(f"  Failed:  {summary['failed']}")
        print(f"  Warning: {summary['warnings']}")
        print(f"  N/A:     {summary['not_applicable']}")
        print("=" * 60)

        # Show failed controls
        failed = [c for c in result['controls'] if c['status'] == 'failed']
        if failed:
            print("\nFailed controls requiring remediation:")
            for control in failed[:5]:
                print(f"\n  [{control['severity'].upper()}] {control['control_id']}")
                print(f"  {control['title']}")
                print(f"  Recommendation: {control['recommendation']}")


def main():
    """Main entry point for CLI."""
    parser = argparse.ArgumentParser(
        description="Check compliance against SOC 2, PCI-DSS, HIPAA, GDPR",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s /path/to/project
  %(prog)s /path/to/project --framework soc2
  %(prog)s /path/to/project --framework pci-dss --output report.json
  %(prog)s . --framework all --verbose
        """
    )

    parser.add_argument(
        "target",
        help="Directory to check for compliance"
    )
    parser.add_argument(
        "--framework", "-f",
        choices=["soc2", "pci-dss", "hipaa", "gdpr", "all"],
        default="all",
        help="Compliance framework to check (default: all)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path"
    )

    args = parser.parse_args()

    checker = ComplianceChecker(
        target_path=args.target,
        framework=args.framework,
        verbose=args.verbose
    )

    result = checker.check()

    if args.json:
        output = json.dumps(result, indent=2)
        if args.output:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"\nResults written to {args.output}")
        else:
            print(output)
    elif args.output:
        with open(args.output, 'w') as f:
            json.dump(result, f, indent=2)
        print(f"\nResults written to {args.output}")

    # Exit with error code based on compliance level
    if result.get('compliance_level') == 'CRITICAL_GAPS':
        sys.exit(2)
    if result.get('compliance_level') == 'NON_COMPLIANT':
        sys.exit(1)


if __name__ == "__main__":
    main()
