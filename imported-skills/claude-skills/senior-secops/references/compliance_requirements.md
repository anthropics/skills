# Compliance Requirements Reference

Comprehensive guide for SOC 2, PCI-DSS, HIPAA, and GDPR compliance requirements.

---

## Table of Contents

- [SOC 2 Type II](#soc-2-type-ii)
- [PCI-DSS](#pci-dss)
- [HIPAA](#hipaa)
- [GDPR](#gdpr)
- [Compliance Automation](#compliance-automation)
- [Audit Preparation](#audit-preparation)

---

## SOC 2 Type II

### Trust Service Criteria

| Criteria | Description | Key Controls |
|----------|-------------|--------------|
| Security | Protection against unauthorized access | Access controls, encryption, monitoring |
| Availability | System uptime and performance | SLAs, redundancy, disaster recovery |
| Processing Integrity | Accurate and complete processing | Data validation, error handling |
| Confidentiality | Protection of confidential information | Encryption, access controls |
| Privacy | Personal information handling | Consent, data minimization |

### Security Controls Checklist

```markdown
## SOC 2 Security Controls

### CC1: Control Environment
- [ ] Security policies documented and approved
- [ ] Organizational structure defined
- [ ] Security roles and responsibilities assigned
- [ ] Background checks performed on employees
- [ ] Security awareness training completed annually

### CC2: Communication and Information
- [ ] Security policies communicated to employees
- [ ] Security incidents reported and tracked
- [ ] External communications about security controls
- [ ] Service level agreements documented

### CC3: Risk Assessment
- [ ] Annual risk assessment performed
- [ ] Risk register maintained
- [ ] Risk treatment plans documented
- [ ] Vendor risk assessments completed
- [ ] Business impact analysis current

### CC4: Monitoring Activities
- [ ] Security monitoring implemented
- [ ] Log aggregation and analysis
- [ ] Vulnerability scanning (weekly)
- [ ] Penetration testing (annual)
- [ ] Security metrics reviewed monthly

### CC5: Control Activities
- [ ] Access control policies enforced
- [ ] MFA enabled for all users
- [ ] Password policy enforced (12+ chars)
- [ ] Access reviews (quarterly)
- [ ] Least privilege principle applied

### CC6: Logical and Physical Access
- [ ] Identity management system
- [ ] Role-based access control
- [ ] Physical access controls
- [ ] Network segmentation
- [ ] Data center security

### CC7: System Operations
- [ ] Change management process
- [ ] Incident management process
- [ ] Problem management process
- [ ] Capacity management
- [ ] Backup and recovery tested

### CC8: Change Management
- [ ] Change control board
- [ ] Change approval workflow
- [ ] Testing requirements documented
- [ ] Rollback procedures
- [ ] Emergency change process

### CC9: Risk Mitigation
- [ ] Insurance coverage
- [ ] Business continuity plan
- [ ] Disaster recovery plan tested
- [ ] Vendor management program
```

### Evidence Collection

```python
def collect_soc2_evidence(period_start: str, period_end: str) -> dict:
    """
    Collect evidence for SOC 2 audit period.

    Returns dictionary organized by Trust Service Criteria.
    """
    evidence = {
        'period': {'start': period_start, 'end': period_end},
        'security': {
            'access_reviews': get_access_reviews(period_start, period_end),
            'vulnerability_scans': get_vulnerability_reports(period_start, period_end),
            'penetration_tests': get_pentest_reports(period_start, period_end),
            'security_incidents': get_incident_reports(period_start, period_end),
            'training_records': get_training_completion(period_start, period_end),
        },
        'availability': {
            'uptime_reports': get_uptime_metrics(period_start, period_end),
            'incident_reports': get_availability_incidents(period_start, period_end),
            'dr_tests': get_dr_test_results(period_start, period_end),
            'backup_tests': get_backup_test_results(period_start, period_end),
        },
        'processing_integrity': {
            'data_validation_logs': get_validation_logs(period_start, period_end),
            'error_reports': get_error_reports(period_start, period_end),
            'reconciliation_reports': get_reconciliation_reports(period_start, period_end),
        },
        'confidentiality': {
            'encryption_status': get_encryption_audit(period_start, period_end),
            'data_classification': get_data_inventory(),
            'access_logs': get_sensitive_data_access_logs(period_start, period_end),
        }
    }

    return evidence
```

---

## PCI-DSS

### PCI-DSS v4.0 Requirements

| Requirement | Description |
|-------------|-------------|
| 1 | Install and maintain network security controls |
| 2 | Apply secure configurations |
| 3 | Protect stored account data |
| 4 | Protect cardholder data with cryptography during transmission |
| 5 | Protect all systems from malware |
| 6 | Develop and maintain secure systems and software |
| 7 | Restrict access to cardholder data by business need-to-know |
| 8 | Identify users and authenticate access |
| 9 | Restrict physical access to cardholder data |
| 10 | Log and monitor all access to network resources |
| 11 | Test security of systems and networks regularly |
| 12 | Support information security with organizational policies |

### Cardholder Data Protection

```python
# PCI-DSS compliant card data handling

import re
from cryptography.fernet import Fernet
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
import base64
import os

class PCIDataHandler:
    """Handle cardholder data per PCI-DSS requirements."""

    # PAN patterns (masked for display)
    PAN_PATTERN = re.compile(r'\b(?:\d{4}[-\s]?){3}\d{4}\b')

    def __init__(self, encryption_key: bytes):
        self.cipher = Fernet(encryption_key)

    @staticmethod
    def mask_pan(pan: str) -> str:
        """
        Mask PAN per PCI-DSS (show first 6, last 4 only).
        Requirement 3.4: Render PAN unreadable.
        """
        digits = re.sub(r'\D', '', pan)
        if len(digits) < 13:
            return '*' * len(digits)
        return f"{digits[:6]}{'*' * (len(digits) - 10)}{digits[-4:]}"

    def encrypt_pan(self, pan: str) -> str:
        """
        Encrypt PAN for storage.
        Requirement 3.5: Protect keys used to protect stored account data.
        """
        return self.cipher.encrypt(pan.encode()).decode()

    def decrypt_pan(self, encrypted_pan: str) -> str:
        """Decrypt PAN (requires authorization logging)."""
        return self.cipher.decrypt(encrypted_pan.encode()).decode()

    @staticmethod
    def validate_pan(pan: str) -> bool:
        """Validate PAN using Luhn algorithm."""
        digits = re.sub(r'\D', '', pan)
        if len(digits) < 13 or len(digits) > 19:
            return False

        # Luhn algorithm
        total = 0
        for i, digit in enumerate(reversed(digits)):
            d = int(digit)
            if i % 2 == 1:
                d *= 2
                if d > 9:
                    d -= 9
            total += d
        return total % 10 == 0

    def sanitize_logs(self, log_message: str) -> str:
        """
        Remove PAN from log messages.
        Requirement 3.3: Mask PAN when displayed.
        """
        def replace_pan(match):
            return self.mask_pan(match.group())

        return self.PAN_PATTERN.sub(replace_pan, log_message)
```

### Network Segmentation

```yaml
# PCI-DSS network segmentation example

# Cardholder Data Environment (CDE) firewall rules
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: cde-isolation
  namespace: payment-processing
spec:
  podSelector:
    matchLabels:
      pci-zone: cde
  policyTypes:
    - Ingress
    - Egress
  ingress:
    # Only allow from payment gateway
    - from:
        - namespaceSelector:
            matchLabels:
              pci-zone: dmz
        - podSelector:
            matchLabels:
              app: payment-gateway
      ports:
        - protocol: TCP
          port: 443
  egress:
    # Only allow to payment processor
    - to:
        - ipBlock:
            cidr: 10.0.100.0/24  # Payment processor network
      ports:
        - protocol: TCP
          port: 443
    # Allow DNS
    - to:
        - namespaceSelector: {}
          podSelector:
            matchLabels:
              k8s-app: kube-dns
      ports:
        - protocol: UDP
          port: 53
```

---

## HIPAA

### HIPAA Security Rule Requirements

| Safeguard | Standard | Implementation |
|-----------|----------|----------------|
| Administrative | Security Management | Risk analysis, sanctions, activity review |
| Administrative | Workforce Security | Authorization, clearance, termination |
| Administrative | Information Access | Access authorization, workstation use |
| Administrative | Security Awareness | Training, login monitoring, password management |
| Administrative | Security Incident | Response and reporting procedures |
| Administrative | Contingency Plan | Backup, disaster recovery, emergency mode |
| Physical | Facility Access | Access controls, maintenance records |
| Physical | Workstation | Use policies, security |
| Physical | Device and Media | Disposal, media re-use, accountability |
| Technical | Access Control | Unique user ID, emergency access, encryption |
| Technical | Audit Controls | Hardware, software, procedural mechanisms |
| Technical | Integrity | Mechanisms to ensure PHI not altered |
| Technical | Transmission | Encryption of PHI in transit |

### PHI Handling

```python
from dataclasses import dataclass
from datetime import datetime
from typing import Optional
import hashlib
import logging

# Configure PHI audit logging
phi_logger = logging.getLogger('phi_access')
phi_logger.setLevel(logging.INFO)

@dataclass
class PHIAccessLog:
    """HIPAA-compliant PHI access logging."""
    timestamp: datetime
    user_id: str
    patient_id: str
    action: str  # view, create, update, delete, export
    reason: str
    data_elements: list
    source_ip: str
    success: bool

def log_phi_access(access: PHIAccessLog):
    """
    Log PHI access per HIPAA requirements.
    164.312(b): Audit controls.
    """
    phi_logger.info(
        f"PHI_ACCESS|"
        f"timestamp={access.timestamp.isoformat()}|"
        f"user={access.user_id}|"
        f"patient={access.patient_id}|"
        f"action={access.action}|"
        f"reason={access.reason}|"
        f"elements={','.join(access.data_elements)}|"
        f"ip={access.source_ip}|"
        f"success={access.success}"
    )

class HIPAACompliantStorage:
    """HIPAA-compliant PHI storage handler."""

    # Minimum Necessary Standard - only access needed data
    PHI_ELEMENTS = {
        'patient_name': 'high',
        'ssn': 'high',
        'medical_record_number': 'high',
        'diagnosis': 'medium',
        'treatment_plan': 'medium',
        'appointment_date': 'low',
        'provider_name': 'low'
    }

    def __init__(self, encryption_service, user_context):
        self.encryption = encryption_service
        self.user = user_context

    def access_phi(
        self,
        patient_id: str,
        elements: list,
        reason: str
    ) -> Optional[dict]:
        """
        Access PHI with HIPAA controls.

        Args:
            patient_id: Patient identifier
            elements: List of PHI elements to access
            reason: Business reason for access

        Returns:
            Requested PHI elements if authorized
        """
        # Verify minimum necessary - user only gets needed elements
        authorized_elements = self._check_authorization(elements)

        if not authorized_elements:
            log_phi_access(PHIAccessLog(
                timestamp=datetime.utcnow(),
                user_id=self.user.id,
                patient_id=patient_id,
                action='view',
                reason=reason,
                data_elements=elements,
                source_ip=self.user.ip_address,
                success=False
            ))
            raise PermissionError("Not authorized for requested PHI elements")

        # Retrieve and decrypt PHI
        phi_data = self._retrieve_phi(patient_id, authorized_elements)

        # Log successful access
        log_phi_access(PHIAccessLog(
            timestamp=datetime.utcnow(),
            user_id=self.user.id,
            patient_id=patient_id,
            action='view',
            reason=reason,
            data_elements=authorized_elements,
            source_ip=self.user.ip_address,
            success=True
        ))

        return phi_data

    def _check_authorization(self, requested_elements: list) -> list:
        """Check user authorization for PHI elements."""
        user_clearance = self.user.hipaa_clearance_level
        authorized = []

        for element in requested_elements:
            element_level = self.PHI_ELEMENTS.get(element, 'high')
            if self._clearance_allows(user_clearance, element_level):
                authorized.append(element)

        return authorized
```

---

## GDPR

### GDPR Principles

| Principle | Description | Implementation |
|-----------|-------------|----------------|
| Lawfulness | Legal basis for processing | Consent management, contract basis |
| Purpose Limitation | Specific, explicit purposes | Data use policies, access controls |
| Data Minimization | Adequate, relevant, limited | Collection limits, retention policies |
| Accuracy | Keep data accurate | Update procedures, validation |
| Storage Limitation | Time-limited retention | Retention schedules, deletion |
| Integrity & Confidentiality | Secure processing | Encryption, access controls |
| Accountability | Demonstrate compliance | Documentation, DPO, DPIA |

### Data Subject Rights Implementation

```python
from datetime import datetime, timedelta
from enum import Enum
from typing import Optional, List
import json

class DSRType(Enum):
    ACCESS = "access"           # Article 15
    RECTIFICATION = "rectification"  # Article 16
    ERASURE = "erasure"         # Article 17 (Right to be forgotten)
    RESTRICTION = "restriction"  # Article 18
    PORTABILITY = "portability"  # Article 20
    OBJECTION = "objection"     # Article 21

class DataSubjectRequest:
    """Handle GDPR Data Subject Requests."""

    # GDPR requires response within 30 days
    RESPONSE_DEADLINE_DAYS = 30

    def __init__(self, db, notification_service):
        self.db = db
        self.notifications = notification_service

    def submit_request(
        self,
        subject_email: str,
        request_type: DSRType,
        details: str
    ) -> dict:
        """
        Submit a Data Subject Request.

        Args:
            subject_email: Email of the data subject
            request_type: Type of GDPR request
            details: Additional request details

        Returns:
            Request tracking information
        """
        # Verify identity before processing
        verification_token = self._send_verification(subject_email)

        request = {
            'id': self._generate_request_id(),
            'subject_email': subject_email,
            'type': request_type.value,
            'details': details,
            'status': 'pending_verification',
            'submitted_at': datetime.utcnow().isoformat(),
            'deadline': (datetime.utcnow() + timedelta(days=self.RESPONSE_DEADLINE_DAYS)).isoformat(),
            'verification_token': verification_token
        }

        self.db.dsr_requests.insert(request)

        # Notify DPO
        self.notifications.notify_dpo(
            f"New DSR ({request_type.value}) received",
            request
        )

        return {
            'request_id': request['id'],
            'deadline': request['deadline'],
            'status': 'verification_sent'
        }

    def process_erasure_request(self, request_id: str) -> dict:
        """
        Process Article 17 erasure request (Right to be Forgotten).

        Returns:
            Erasure completion report
        """
        request = self.db.dsr_requests.find_one({'id': request_id})
        subject_email = request['subject_email']

        erasure_report = {
            'request_id': request_id,
            'subject': subject_email,
            'systems_processed': [],
            'data_deleted': [],
            'data_retained': [],  # With legal basis
            'completed_at': None
        }

        # Find all data for this subject
        data_inventory = self._find_subject_data(subject_email)

        for data_item in data_inventory:
            if self._can_delete(data_item):
                self._delete_data(data_item)
                erasure_report['data_deleted'].append({
                    'system': data_item['system'],
                    'data_type': data_item['type'],
                    'deleted_at': datetime.utcnow().isoformat()
                })
            else:
                erasure_report['data_retained'].append({
                    'system': data_item['system'],
                    'data_type': data_item['type'],
                    'retention_reason': data_item['legal_basis']
                })

        erasure_report['completed_at'] = datetime.utcnow().isoformat()

        # Update request status
        self.db.dsr_requests.update(
            {'id': request_id},
            {'status': 'completed', 'completion_report': erasure_report}
        )

        return erasure_report

    def generate_portability_export(self, request_id: str) -> dict:
        """
        Generate Article 20 data portability export.

        Returns machine-readable export in JSON format.
        """
        request = self.db.dsr_requests.find_one({'id': request_id})
        subject_email = request['subject_email']

        export_data = {
            'export_date': datetime.utcnow().isoformat(),
            'data_subject': subject_email,
            'format': 'JSON',
            'data': {}
        }

        # Collect data from all systems
        systems = ['user_accounts', 'orders', 'preferences', 'communications']

        for system in systems:
            system_data = self._extract_portable_data(system, subject_email)
            if system_data:
                export_data['data'][system] = system_data

        return export_data
```

### Consent Management

```python
class ConsentManager:
    """GDPR-compliant consent management."""

    def __init__(self, db):
        self.db = db

    def record_consent(
        self,
        user_id: str,
        purpose: str,
        consent_given: bool,
        consent_text: str
    ) -> dict:
        """
        Record consent per GDPR Article 7 requirements.

        Consent must be:
        - Freely given
        - Specific
        - Informed
        - Unambiguous
        """
        consent_record = {
            'user_id': user_id,
            'purpose': purpose,
            'consent_given': consent_given,
            'consent_text': consent_text,
            'timestamp': datetime.utcnow().isoformat(),
            'method': 'explicit_checkbox',  # Not pre-ticked
            'ip_address': self._get_user_ip(),
            'user_agent': self._get_user_agent(),
            'version': '1.0'  # Track consent version
        }

        self.db.consents.insert(consent_record)

        return consent_record

    def check_consent(self, user_id: str, purpose: str) -> bool:
        """Check if user has given consent for specific purpose."""
        latest_consent = self.db.consents.find_one(
            {'user_id': user_id, 'purpose': purpose},
            sort=[('timestamp', -1)]
        )

        return latest_consent and latest_consent.get('consent_given', False)

    def withdraw_consent(self, user_id: str, purpose: str) -> dict:
        """
        Process consent withdrawal.

        GDPR Article 7(3): Withdrawal must be as easy as giving consent.
        """
        withdrawal_record = {
            'user_id': user_id,
            'purpose': purpose,
            'consent_given': False,
            'timestamp': datetime.utcnow().isoformat(),
            'action': 'withdrawal'
        }

        self.db.consents.insert(withdrawal_record)

        # Trigger data processing stop for this purpose
        self._stop_processing(user_id, purpose)

        return withdrawal_record
```

---

## Compliance Automation

### Automated Compliance Checks

```yaml
# compliance-checks.yml - GitHub Actions

name: Compliance Checks

on:
  push:
    branches: [main]
  pull_request:
  schedule:
    - cron: '0 0 * * *'  # Daily

jobs:
  soc2-checks:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Check for secrets in code
        run: |
          gitleaks detect --source . --report-format json --report-path gitleaks-report.json
          if [ -s gitleaks-report.json ]; then
            echo "Secrets detected in code!"
            exit 1
          fi

      - name: Verify encryption at rest
        run: |
          # Check database encryption configuration
          python scripts/compliance_checker.py --check encryption

      - name: Verify access controls
        run: |
          # Check RBAC configuration
          python scripts/compliance_checker.py --check access-control

      - name: Check logging configuration
        run: |
          # Verify audit logging enabled
          python scripts/compliance_checker.py --check audit-logging

  pci-checks:
    runs-on: ubuntu-latest
    if: contains(github.event.head_commit.message, '[pci]')
    steps:
      - uses: actions/checkout@v4

      - name: Scan for PAN in code
        run: |
          # Check for unencrypted card numbers
          python scripts/compliance_checker.py --check pci-pan-exposure

      - name: Verify TLS configuration
        run: |
          python scripts/compliance_checker.py --check tls-config

  gdpr-checks:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Check data retention policies
        run: |
          python scripts/compliance_checker.py --check data-retention

      - name: Verify consent mechanisms
        run: |
          python scripts/compliance_checker.py --check consent-management
```

---

## Audit Preparation

### Audit Readiness Checklist

```markdown
## Pre-Audit Checklist

### 60 Days Before Audit
- [ ] Confirm audit scope and timeline
- [ ] Identify control owners
- [ ] Begin evidence collection
- [ ] Review previous audit findings
- [ ] Update policies and procedures

### 30 Days Before Audit
- [ ] Complete evidence collection
- [ ] Perform internal control testing
- [ ] Remediate any gaps identified
- [ ] Prepare executive summary
- [ ] Brief stakeholders

### 7 Days Before Audit
- [ ] Finalize evidence package
- [ ] Prepare interview schedules
- [ ] Set up secure evidence sharing
- [ ] Confirm auditor logistics
- [ ] Final gap assessment

### During Audit
- [ ] Daily status meetings
- [ ] Timely evidence delivery
- [ ] Document all requests
- [ ] Escalate issues promptly
- [ ] Maintain communication log
```

### Evidence Repository Structure

```
evidence/
├── period_YYYY-MM/
│   ├── security/
│   │   ├── access_reviews/
│   │   ├── vulnerability_scans/
│   │   ├── penetration_tests/
│   │   └── security_training/
│   ├── availability/
│   │   ├── uptime_reports/
│   │   ├── incident_reports/
│   │   └── dr_tests/
│   ├── change_management/
│   │   ├── change_requests/
│   │   ├── approval_records/
│   │   └── deployment_logs/
│   ├── policies/
│   │   ├── current_policies/
│   │   └── acknowledgments/
│   └── index.json
```
