#!/usr/bin/env python3
"""
DPIA Generator

Generates Data Protection Impact Assessment documentation based on
processing activity inputs. Creates structured DPIA reports following
GDPR Article 35 requirements.

Usage:
    python dpia_generator.py --interactive
    python dpia_generator.py --input processing_activity.json --output dpia_report.md
    python dpia_generator.py --template > template.json
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional


# DPIA threshold criteria (Art. 35(3) and WP29 Guidelines)
DPIA_TRIGGERS = {
    "systematic_monitoring": {
        "description": "Systematic monitoring of publicly accessible area",
        "article": "Art. 35(3)(c)",
        "weight": 10
    },
    "large_scale_special_category": {
        "description": "Large-scale processing of special category data (Art. 9)",
        "article": "Art. 35(3)(b)",
        "weight": 10
    },
    "automated_decision_making": {
        "description": "Automated decision-making with legal/significant effects",
        "article": "Art. 35(3)(a)",
        "weight": 10
    },
    "evaluation_scoring": {
        "description": "Evaluation or scoring of individuals",
        "article": "WP29 Guidelines",
        "weight": 7
    },
    "sensitive_data": {
        "description": "Processing of sensitive data or highly personal data",
        "article": "WP29 Guidelines",
        "weight": 7
    },
    "large_scale": {
        "description": "Data processed on a large scale",
        "article": "WP29 Guidelines",
        "weight": 6
    },
    "data_matching": {
        "description": "Matching or combining datasets",
        "article": "WP29 Guidelines",
        "weight": 5
    },
    "vulnerable_subjects": {
        "description": "Data concerning vulnerable data subjects",
        "article": "WP29 Guidelines",
        "weight": 7
    },
    "innovative_technology": {
        "description": "Innovative use or applying new technological solutions",
        "article": "WP29 Guidelines",
        "weight": 5
    },
    "cross_border_transfer": {
        "description": "Transfer of data outside the EU/EEA",
        "article": "GDPR Chapter V",
        "weight": 5
    }
}

# Risk categories and mitigation measures
RISK_CATEGORIES = {
    "unauthorized_access": {
        "description": "Risk of unauthorized access to personal data",
        "impact": "high",
        "mitigations": [
            "Implement access controls and authentication",
            "Use encryption for data at rest and in transit",
            "Maintain audit logs of access",
            "Implement least privilege principle"
        ]
    },
    "data_breach": {
        "description": "Risk of data breach or unauthorized disclosure",
        "impact": "high",
        "mitigations": [
            "Implement intrusion detection systems",
            "Establish incident response procedures",
            "Regular security assessments",
            "Employee security training"
        ]
    },
    "excessive_collection": {
        "description": "Risk of collecting more data than necessary",
        "impact": "medium",
        "mitigations": [
            "Implement data minimization principles",
            "Regular review of data collected",
            "Privacy by design approach",
            "Document purpose for each data element"
        ]
    },
    "purpose_creep": {
        "description": "Risk of using data for purposes beyond original scope",
        "impact": "medium",
        "mitigations": [
            "Clear purpose limitation policies",
            "Consent management for new purposes",
            "Technical controls on data access",
            "Regular purpose review"
        ]
    },
    "retention_violation": {
        "description": "Risk of retaining data longer than necessary",
        "impact": "medium",
        "mitigations": [
            "Implement retention schedules",
            "Automated deletion processes",
            "Regular data inventory audits",
            "Document retention justification"
        ]
    },
    "rights_violation": {
        "description": "Risk of failing to fulfill data subject rights",
        "impact": "high",
        "mitigations": [
            "Implement subject access request process",
            "Technical capability for data portability",
            "Deletion/erasure procedures",
            "Staff training on rights requests"
        ]
    },
    "inaccurate_data": {
        "description": "Risk of processing inaccurate or outdated data",
        "impact": "medium",
        "mitigations": [
            "Data quality checks at collection",
            "Regular data verification",
            "Easy update mechanisms for subjects",
            "Automated accuracy validation"
        ]
    },
    "third_party_risk": {
        "description": "Risk from third-party processors",
        "impact": "high",
        "mitigations": [
            "Due diligence on processors",
            "Data Processing Agreements",
            "Regular processor audits",
            "Clear processor instructions"
        ]
    }
}

# Legal bases under Article 6
LEGAL_BASES = {
    "consent": {
        "article": "Art. 6(1)(a)",
        "description": "Data subject has given consent",
        "requirements": [
            "Consent must be freely given",
            "Specific to the purpose",
            "Informed consent with clear information",
            "Unambiguous indication of wishes",
            "Easy to withdraw"
        ]
    },
    "contract": {
        "article": "Art. 6(1)(b)",
        "description": "Processing necessary for contract performance",
        "requirements": [
            "Contract must exist or be in negotiation",
            "Processing must be necessary for the contract",
            "Cannot process more than contractually needed"
        ]
    },
    "legal_obligation": {
        "article": "Art. 6(1)(c)",
        "description": "Processing necessary for legal obligation",
        "requirements": [
            "Legal obligation must be binding",
            "Must be EU or Member State law",
            "Processing must be necessary to comply"
        ]
    },
    "vital_interests": {
        "article": "Art. 6(1)(d)",
        "description": "Processing necessary to protect vital interests",
        "requirements": [
            "Life-threatening situation",
            "No other legal basis available",
            "Typically emergency situations"
        ]
    },
    "public_interest": {
        "article": "Art. 6(1)(e)",
        "description": "Processing necessary for public interest task",
        "requirements": [
            "Task in public interest or official authority",
            "Legal basis in EU or Member State law",
            "Processing must be necessary"
        ]
    },
    "legitimate_interests": {
        "article": "Art. 6(1)(f)",
        "description": "Processing necessary for legitimate interests",
        "requirements": [
            "Identify the legitimate interest",
            "Show processing is necessary",
            "Balance against data subject rights",
            "Not available for public authorities"
        ]
    }
}


def get_template() -> Dict:
    """Return a blank DPIA input template."""
    return {
        "project_name": "",
        "version": "1.0",
        "date": datetime.now().strftime("%Y-%m-%d"),
        "controller": {
            "name": "",
            "contact": "",
            "dpo_contact": ""
        },
        "processing_activity": {
            "description": "",
            "purposes": [],
            "legal_basis": "",
            "legal_basis_justification": ""
        },
        "data_subjects": {
            "categories": [],
            "estimated_number": "",
            "vulnerable_groups": False,
            "vulnerable_groups_details": ""
        },
        "personal_data": {
            "categories": [],
            "special_categories": [],
            "source": "",
            "retention_period": ""
        },
        "processing_operations": {
            "collection_method": "",
            "storage_location": "",
            "access_controls": "",
            "automated_decisions": False,
            "profiling": False
        },
        "data_recipients": {
            "internal": [],
            "external_processors": [],
            "third_countries": []
        },
        "dpia_triggers": [],
        "identified_risks": [],
        "mitigations_planned": []
    }


def assess_dpia_requirement(input_data: Dict) -> Dict:
    """Assess whether DPIA is required based on triggers."""
    triggers_present = input_data.get("dpia_triggers", [])
    total_weight = 0
    triggered_criteria = []

    for trigger in triggers_present:
        if trigger in DPIA_TRIGGERS:
            trigger_info = DPIA_TRIGGERS[trigger]
            total_weight += trigger_info["weight"]
            triggered_criteria.append({
                "trigger": trigger,
                "description": trigger_info["description"],
                "article": trigger_info["article"]
            })

    # Also check data characteristics
    if input_data.get("data_subjects", {}).get("vulnerable_groups"):
        if "vulnerable_subjects" not in triggers_present:
            total_weight += DPIA_TRIGGERS["vulnerable_subjects"]["weight"]
            triggered_criteria.append({
                "trigger": "vulnerable_subjects",
                "description": DPIA_TRIGGERS["vulnerable_subjects"]["description"],
                "article": DPIA_TRIGGERS["vulnerable_subjects"]["article"]
            })

    if input_data.get("personal_data", {}).get("special_categories"):
        if "sensitive_data" not in triggers_present:
            total_weight += DPIA_TRIGGERS["sensitive_data"]["weight"]
            triggered_criteria.append({
                "trigger": "sensitive_data",
                "description": DPIA_TRIGGERS["sensitive_data"]["description"],
                "article": DPIA_TRIGGERS["sensitive_data"]["article"]
            })

    if input_data.get("data_recipients", {}).get("third_countries"):
        if "cross_border_transfer" not in triggers_present:
            total_weight += DPIA_TRIGGERS["cross_border_transfer"]["weight"]
            triggered_criteria.append({
                "trigger": "cross_border_transfer",
                "description": DPIA_TRIGGERS["cross_border_transfer"]["description"],
                "article": DPIA_TRIGGERS["cross_border_transfer"]["article"]
            })

    # DPIA required if 2+ triggers or weight >= 10
    dpia_required = len(triggered_criteria) >= 2 or total_weight >= 10

    return {
        "dpia_required": dpia_required,
        "risk_score": total_weight,
        "triggered_criteria": triggered_criteria,
        "recommendation": "DPIA is mandatory" if dpia_required else "DPIA recommended as best practice"
    }


def assess_risks(input_data: Dict) -> List[Dict]:
    """Assess risks based on processing characteristics."""
    risks = []

    # Check each risk category
    processing = input_data.get("processing_operations", {})
    recipients = input_data.get("data_recipients", {})
    personal_data = input_data.get("personal_data", {})

    # Unauthorized access risk
    if processing.get("storage_location") or processing.get("collection_method"):
        risks.append({
            **RISK_CATEGORIES["unauthorized_access"],
            "likelihood": "medium",
            "residual_risk": "low" if processing.get("access_controls") else "medium"
        })

    # Data breach risk (always present)
    risks.append({
        **RISK_CATEGORIES["data_breach"],
        "likelihood": "medium",
        "residual_risk": "medium"
    })

    # Third party risk
    if recipients.get("external_processors") or recipients.get("third_countries"):
        risks.append({
            **RISK_CATEGORIES["third_party_risk"],
            "likelihood": "medium",
            "residual_risk": "medium"
        })

    # Rights violation risk
    risks.append({
        **RISK_CATEGORIES["rights_violation"],
        "likelihood": "low",
        "residual_risk": "low"
    })

    # Retention violation risk
    if not personal_data.get("retention_period"):
        risks.append({
            **RISK_CATEGORIES["retention_violation"],
            "likelihood": "high",
            "residual_risk": "high"
        })

    # Automated decision risk
    if processing.get("automated_decisions") or processing.get("profiling"):
        risks.append({
            "description": "Risk of unfair automated decisions affecting individuals",
            "impact": "high",
            "likelihood": "medium",
            "residual_risk": "medium",
            "mitigations": [
                "Human review of automated decisions",
                "Transparency about logic involved",
                "Right to contest decisions",
                "Regular algorithm audits"
            ]
        })

    return risks


def generate_dpia_report(input_data: Dict) -> str:
    """Generate DPIA report in Markdown format."""
    requirement = assess_dpia_requirement(input_data)
    risks = assess_risks(input_data)

    project = input_data.get("project_name", "Unnamed Project")
    controller = input_data.get("controller", {})
    processing = input_data.get("processing_activity", {})
    subjects = input_data.get("data_subjects", {})
    personal_data = input_data.get("personal_data", {})
    operations = input_data.get("processing_operations", {})
    recipients = input_data.get("data_recipients", {})

    legal_basis = processing.get("legal_basis", "")
    legal_info = LEGAL_BASES.get(legal_basis, {})

    report = f"""# Data Protection Impact Assessment (DPIA)

## Project: {project}

| Field | Value |
|-------|-------|
| Version | {input_data.get('version', '1.0')} |
| Date | {input_data.get('date', datetime.now().strftime('%Y-%m-%d'))} |
| Controller | {controller.get('name', 'N/A')} |
| DPO Contact | {controller.get('dpo_contact', 'N/A')} |

---

## 1. DPIA Threshold Assessment

**Result: {requirement['recommendation']}**

Risk Score: {requirement['risk_score']}/100

### Triggered Criteria

"""
    if requirement['triggered_criteria']:
        for criteria in requirement['triggered_criteria']:
            report += f"- **{criteria['description']}** ({criteria['article']})\n"
    else:
        report += "- No mandatory triggers identified\n"

    report += f"""
---

## 2. Description of Processing

### Purpose of Processing

{processing.get('description', 'Not specified')}

### Purposes

"""
    for purpose in processing.get('purposes', ['Not specified']):
        report += f"- {purpose}\n"

    report += f"""
### Legal Basis

**{legal_info.get('article', 'Not specified')}**: {legal_info.get('description', processing.get('legal_basis', 'Not specified'))}

**Justification**: {processing.get('legal_basis_justification', 'Not provided')}

"""
    if legal_info.get('requirements'):
        report += "**Requirements to satisfy:**\n"
        for req in legal_info['requirements']:
            report += f"- {req}\n"

    report += f"""
---

## 3. Data Subjects

| Aspect | Details |
|--------|---------|
| Categories | {', '.join(subjects.get('categories', ['Not specified']))} |
| Estimated Number | {subjects.get('estimated_number', 'Not specified')} |
| Vulnerable Groups | {'Yes - ' + subjects.get('vulnerable_groups_details', '') if subjects.get('vulnerable_groups') else 'No'} |

---

## 4. Personal Data Processed

### Data Categories

"""
    for category in personal_data.get('categories', ['Not specified']):
        report += f"- {category}\n"

    if personal_data.get('special_categories'):
        report += "\n### Special Category Data (Art. 9)\n\n"
        for category in personal_data['special_categories']:
            report += f"- **{category}** - Requires Art. 9(2) exception\n"

    report += f"""
### Data Source

{personal_data.get('source', 'Not specified')}

### Retention Period

{personal_data.get('retention_period', 'Not specified')}

---

## 5. Processing Operations

| Operation | Details |
|-----------|---------|
| Collection Method | {operations.get('collection_method', 'Not specified')} |
| Storage Location | {operations.get('storage_location', 'Not specified')} |
| Access Controls | {operations.get('access_controls', 'Not specified')} |
| Automated Decisions | {'Yes' if operations.get('automated_decisions') else 'No'} |
| Profiling | {'Yes' if operations.get('profiling') else 'No'} |

---

## 6. Data Recipients

### Internal Recipients

"""
    for recipient in recipients.get('internal', ['Not specified']):
        report += f"- {recipient}\n"

    report += "\n### External Processors\n\n"
    for processor in recipients.get('external_processors', ['None']):
        report += f"- {processor}\n"

    if recipients.get('third_countries'):
        report += "\n### Third Country Transfers\n\n"
        report += "**Warning**: Transfers require Chapter V safeguards\n\n"
        for country in recipients['third_countries']:
            report += f"- {country}\n"

    report += """
---

## 7. Risk Assessment

"""
    for i, risk in enumerate(risks, 1):
        report += f"""### Risk {i}: {risk['description']}

| Aspect | Assessment |
|--------|------------|
| Impact | {risk.get('impact', 'medium').upper()} |
| Likelihood | {risk.get('likelihood', 'medium').upper()} |
| Residual Risk | {risk.get('residual_risk', 'medium').upper()} |

**Recommended Mitigations:**

"""
        for mitigation in risk.get('mitigations', []):
            report += f"- {mitigation}\n"
        report += "\n"

    report += """---

## 8. Necessity and Proportionality

### Assessment Questions

1. **Is the processing necessary for the stated purpose?**
   - [ ] Yes, no less intrusive alternative exists
   - [ ] Alternative considered: _______________

2. **Is the data collection proportionate?**
   - [ ] Only necessary data is collected
   - [ ] Data minimization applied

3. **Are retention periods justified?**
   - [ ] Retention period is necessary
   - [ ] Deletion procedures in place

---

## 9. DPO Consultation

| Aspect | Details |
|--------|---------|
| DPO Consulted | [ ] Yes / [ ] No |
| DPO Name | |
| Consultation Date | |
| DPO Opinion | |

---

## 10. Sign-Off

| Role | Name | Signature | Date |
|------|------|-----------|------|
| Project Owner | | | |
| Data Protection Officer | | | |
| Controller Representative | | | |

---

## 11. Review Schedule

This DPIA should be reviewed:
- [ ] Annually
- [ ] When processing changes significantly
- [ ] Following a data incident
- [ ] As required by supervisory authority

Next Review Date: _______________

---

*Generated by DPIA Generator - This document requires completion and review by qualified personnel.*
"""
    return report


def main():
    parser = argparse.ArgumentParser(
        description="Generate DPIA documentation"
    )
    parser.add_argument(
        "--input", "-i",
        help="Path to JSON input file with processing activity details"
    )
    parser.add_argument(
        "--output", "-o",
        help="Path to output file (default: stdout)"
    )
    parser.add_argument(
        "--template",
        action="store_true",
        help="Output a blank JSON template"
    )
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run in interactive mode"
    )

    args = parser.parse_args()

    if args.template:
        print(json.dumps(get_template(), indent=2))
        return

    if args.interactive:
        print("DPIA Generator - Interactive Mode")
        print("=" * 40)
        print("\nTo use this tool:")
        print("1. Generate a template: python dpia_generator.py --template > input.json")
        print("2. Fill in the template with your processing details")
        print("3. Generate DPIA: python dpia_generator.py --input input.json --output dpia.md")
        return

    if not args.input:
        print("Error: --input required (or use --template to get started)")
        sys.exit(1)

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file not found: {input_path}")
        sys.exit(1)

    with open(input_path, "r") as f:
        input_data = json.load(f)

    report = generate_dpia_report(input_data)

    if args.output:
        with open(args.output, "w") as f:
            f.write(report)
        print(f"DPIA report written to {args.output}")
    else:
        print(report)


if __name__ == "__main__":
    main()
