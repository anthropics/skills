#!/usr/bin/env python3
"""
QMS Documentation Checker (legacy-QSR checklist mapped to ISO 13485:2016 under the QMSR)

Assesses quality system documentation against a checklist organized by the
HISTORICAL Quality System Regulation (QSR) subsection structure of 21 CFR Part 820.

IMPORTANT — QMSR transition: FDA's Quality Management System Regulation (QMSR)
final rule (89 FR 7496) took effect 2026-02-02. It amended 21 CFR Part 820 to
incorporate ISO 13485:2016 by reference and REMOVED the legacy QSR subsections
(820.20-820.198) used as keys below. Those numbers are retained here only as a
familiar checklist index; each maps to the ISO 13485:2016 clause that is the
current legal authority (see QSR_TO_ISO13485). This tool checks documentation
coverage — it does not determine current-law compliance.

Usage:
    python qsr_compliance_checker.py <project_dir>
    python qsr_compliance_checker.py <project_dir> --section 820.30
    python qsr_compliance_checker.py <project_dir> --json
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any


# Historical QSR section -> current QMSR / ISO 13485:2016 authority
# (legacy subsections removed by the QMSR effective 2026-02-02)
QSR_TO_ISO13485 = {
    "820.20": "ISO 13485 §5.1/5.5/5.6",
    "820.30": "ISO 13485 §7.3",
    "820.40": "ISO 13485 §4.2.4",
    "820.50": "ISO 13485 §7.4",
    "820.70": "ISO 13485 §6.3/6.4/7.5.1",
    "820.72": "ISO 13485 §7.6",
    "820.75": "ISO 13485 §7.5.6",
    "820.90": "ISO 13485 §8.3",
    "820.100": "ISO 13485 §8.5.2/8.5.3",
    "820.120": "21 CFR 820.45 (retained) + ISO 13485 §7.5.1",
    "820.180": "ISO 13485 §4.2.5 + 21 CFR 820.35 (retained)",
    "820.181": "ISO 13485 §4.2.3 (medical device file)",
    "820.184": "ISO 13485 §4.2.5 + 21 CFR 820.35",
    "820.198": "ISO 13485 §8.2.2 + 21 CFR 820.35(b)",
}

# Legacy QSR sections and requirements (historical index; see QSR_TO_ISO13485 for current authority)
QSR_REQUIREMENTS = {
    "820.20": {
        "title": "Management Responsibility",
        "subsections": {
            "820.20(a)": {
                "title": "Quality Policy",
                "required_evidence": ["quality_policy", "quality_manual", "quality_objectives"],
                "doc_patterns": ["quality_policy*", "quality_manual*", "qms_manual*"],
                "keywords": ["quality policy", "quality objectives", "management commitment"]
            },
            "820.20(b)": {
                "title": "Organization",
                "required_evidence": ["org_chart", "job_descriptions", "authority_matrix"],
                "doc_patterns": ["org_chart*", "organization*", "job_desc*", "authority*"],
                "keywords": ["organizational structure", "responsibility", "authority"]
            },
            "820.20(c)": {
                "title": "Management Review",
                "required_evidence": ["management_review_procedure", "management_review_records"],
                "doc_patterns": ["management_review*", "mgmt_review*", "qmr*"],
                "keywords": ["management review", "review meeting", "quality system effectiveness"]
            }
        }
    },
    "820.30": {
        "title": "Design Controls",
        "subsections": {
            "820.30(a)": {
                "title": "Design and Development Planning",
                "required_evidence": ["design_plan", "development_plan"],
                "doc_patterns": ["design_plan*", "dev_plan*", "development_plan*"],
                "keywords": ["design planning", "development phases", "design milestones"]
            },
            "820.30(b)": {
                "title": "Design Input",
                "required_evidence": ["design_input", "requirements_specification"],
                "doc_patterns": ["design_input*", "requirement*", "srs*", "prs*"],
                "keywords": ["design input", "requirements", "user needs", "intended use"]
            },
            "820.30(c)": {
                "title": "Design Output",
                "required_evidence": ["design_output", "specifications", "drawings"],
                "doc_patterns": ["design_output*", "specification*", "drawing*", "bom*"],
                "keywords": ["design output", "specifications", "acceptance criteria"]
            },
            "820.30(d)": {
                "title": "Design Review",
                "required_evidence": ["design_review_procedure", "design_review_records"],
                "doc_patterns": ["design_review*", "dr_record*", "dr_minutes*"],
                "keywords": ["design review", "review meeting", "design evaluation"]
            },
            "820.30(e)": {
                "title": "Design Verification",
                "required_evidence": ["verification_plan", "verification_results"],
                "doc_patterns": ["verification*", "test_report*", "dv_*"],
                "keywords": ["verification", "testing", "design verification"]
            },
            "820.30(f)": {
                "title": "Design Validation",
                "required_evidence": ["validation_plan", "validation_results"],
                "doc_patterns": ["validation*", "clinical*", "usability*", "val_*"],
                "keywords": ["validation", "user needs", "intended use", "clinical evaluation"]
            },
            "820.30(g)": {
                "title": "Design Transfer",
                "required_evidence": ["transfer_checklist", "transfer_verification"],
                "doc_patterns": ["transfer*", "production_release*"],
                "keywords": ["design transfer", "manufacturing", "production"]
            },
            "820.30(h)": {
                "title": "Design Changes",
                "required_evidence": ["change_control_procedure", "change_records"],
                "doc_patterns": ["change_control*", "ecn*", "eco*", "dcr*"],
                "keywords": ["design change", "change control", "modification"]
            },
            "820.30(i)": {
                "title": "Design History File",
                "required_evidence": ["dhf_index", "dhf"],
                "doc_patterns": ["dhf*", "design_history*"],
                "keywords": ["design history file", "DHF", "design records"]
            }
        }
    },
    "820.40": {
        "title": "Document Controls",
        "subsections": {
            "820.40(a)": {
                "title": "Document Approval and Distribution",
                "required_evidence": ["document_control_procedure"],
                "doc_patterns": ["document_control*", "doc_control*", "sop_document*"],
                "keywords": ["document approval", "document distribution", "controlled documents"]
            },
            "820.40(b)": {
                "title": "Document Changes",
                "required_evidence": ["document_change_procedure", "revision_history"],
                "doc_patterns": ["revision_history*", "document_change*"],
                "keywords": ["document change", "revision", "document modification"]
            }
        }
    },
    "820.50": {
        "title": "Purchasing Controls",
        "subsections": {
            "820.50(a)": {
                "title": "Evaluation of Suppliers",
                "required_evidence": ["supplier_qualification_procedure", "approved_supplier_list"],
                "doc_patterns": ["supplier*", "asl*", "vendor*"],
                "keywords": ["supplier evaluation", "approved supplier", "vendor qualification"]
            },
            "820.50(b)": {
                "title": "Purchasing Data",
                "required_evidence": ["purchasing_procedure", "purchase_order_requirements"],
                "doc_patterns": ["purchas*", "procurement*"],
                "keywords": ["purchasing data", "specifications", "quality requirements"]
            }
        }
    },
    "820.70": {
        "title": "Production and Process Controls",
        "subsections": {
            "820.70(a)": {
                "title": "General Process Controls",
                "required_evidence": ["manufacturing_procedures", "work_instructions"],
                "doc_patterns": ["manufacturing*", "production*", "work_instruction*", "wi_*"],
                "keywords": ["manufacturing process", "production", "process parameters"]
            },
            "820.70(b)": {
                "title": "Production and Process Changes",
                "required_evidence": ["process_change_procedure"],
                "doc_patterns": ["process_change*", "manufacturing_change*"],
                "keywords": ["process change", "production change", "change control"]
            },
            "820.70(c)": {
                "title": "Environmental Control",
                "required_evidence": ["environmental_control_procedure", "monitoring_records"],
                "doc_patterns": ["environmental*", "cleanroom*", "env_monitoring*"],
                "keywords": ["environmental control", "cleanroom", "contamination"]
            },
            "820.70(d)": {
                "title": "Personnel",
                "required_evidence": ["training_procedure", "training_records"],
                "doc_patterns": ["training*", "personnel*", "competency*"],
                "keywords": ["training", "personnel qualification", "competency"]
            },
            "820.70(e)": {
                "title": "Contamination Control",
                "required_evidence": ["contamination_control_procedure"],
                "doc_patterns": ["contamination*", "cleaning*", "hygiene*"],
                "keywords": ["contamination", "cleaning", "hygiene"]
            },
            "820.70(f)": {
                "title": "Buildings",
                "required_evidence": ["facility_requirements"],
                "doc_patterns": ["facility*", "building*"],
                "keywords": ["facility", "buildings", "manufacturing area"]
            },
            "820.70(g)": {
                "title": "Equipment",
                "required_evidence": ["equipment_maintenance_procedure", "maintenance_records"],
                "doc_patterns": ["equipment*", "maintenance*", "preventive_maintenance*"],
                "keywords": ["equipment", "maintenance", "calibration"]
            },
            "820.70(h)": {
                "title": "Manufacturing Material",
                "required_evidence": ["material_handling_procedure"],
                "doc_patterns": ["material*", "handling*", "storage*"],
                "keywords": ["manufacturing material", "handling", "storage"]
            },
            "820.70(i)": {
                "title": "Automated Processes",
                "required_evidence": ["software_validation", "automated_process_validation"],
                "doc_patterns": ["software_val*", "csv*", "automation*"],
                "keywords": ["software validation", "automated", "computer system"]
            }
        }
    },
    "820.72": {
        "title": "Inspection, Measuring, and Test Equipment",
        "subsections": {
            "820.72(a)": {
                "title": "Calibration",
                "required_evidence": ["calibration_procedure", "calibration_records"],
                "doc_patterns": ["calibration*", "cal_*"],
                "keywords": ["calibration", "accuracy", "measurement"]
            },
            "820.72(b)": {
                "title": "Calibration Standards",
                "required_evidence": ["calibration_standards", "traceability_records"],
                "doc_patterns": ["calibration_standard*", "nist*", "traceability*"],
                "keywords": ["calibration standards", "NIST", "traceability"]
            }
        }
    },
    "820.75": {
        "title": "Process Validation",
        "subsections": {
            "820.75(a)": {
                "title": "Process Validation Requirements",
                "required_evidence": ["process_validation_procedure", "validation_protocols"],
                "doc_patterns": ["process_validation*", "pv_*", "validation_protocol*"],
                "keywords": ["process validation", "IQ", "OQ", "PQ"]
            },
            "820.75(b)": {
                "title": "Validation Monitoring",
                "required_evidence": ["validation_monitoring", "revalidation_criteria"],
                "doc_patterns": ["revalidation*", "validation_monitoring*"],
                "keywords": ["monitoring", "revalidation", "process performance"]
            }
        }
    },
    "820.90": {
        "title": "Nonconforming Product",
        "subsections": {
            "820.90(a)": {
                "title": "Nonconforming Product Control",
                "required_evidence": ["ncr_procedure", "nonconforming_records"],
                "doc_patterns": ["ncr*", "nonconform*", "nc_*"],
                "keywords": ["nonconforming", "NCR", "disposition"]
            },
            "820.90(b)": {
                "title": "Nonconformance Review",
                "required_evidence": ["ncr_review_procedure"],
                "doc_patterns": ["ncr_review*", "mrb*"],
                "keywords": ["review", "disposition", "concession"]
            }
        }
    },
    "820.100": {
        "title": "Corrective and Preventive Action",
        "subsections": {
            "820.100(a)": {
                "title": "CAPA Procedure",
                "required_evidence": ["capa_procedure", "capa_records"],
                "doc_patterns": ["capa*", "corrective*", "preventive*"],
                "keywords": ["CAPA", "corrective action", "preventive action", "root cause"]
            }
        }
    },
    "820.120": {
        "title": "Device Labeling",
        "subsections": {
            "820.120": {
                "title": "Labeling Controls",
                "required_evidence": ["labeling_procedure", "label_inspection"],
                "doc_patterns": ["label*", "labeling*"],
                "keywords": ["labeling", "label inspection", "UDI"]
            }
        }
    },
    "820.180": {
        "title": "General Requirements - Records",
        "subsections": {
            "820.180": {
                "title": "Records Requirements",
                "required_evidence": ["records_management_procedure", "retention_schedule"],
                "doc_patterns": ["record*", "retention*", "archive*"],
                "keywords": ["records", "retention", "archive", "backup"]
            }
        }
    },
    "820.181": {
        "title": "Device Master Record",
        "subsections": {
            "820.181": {
                "title": "DMR Contents",
                "required_evidence": ["dmr_index", "dmr"],
                "doc_patterns": ["dmr*", "device_master*"],
                "keywords": ["device master record", "DMR", "specifications"]
            }
        }
    },
    "820.184": {
        "title": "Device History Record",
        "subsections": {
            "820.184": {
                "title": "DHR Contents",
                "required_evidence": ["dhr_template", "dhr_records"],
                "doc_patterns": ["dhr*", "device_history*", "batch_record*"],
                "keywords": ["device history record", "DHR", "production record"]
            }
        }
    },
    "820.198": {
        "title": "Complaint Files",
        "subsections": {
            "820.198": {
                "title": "Complaint Handling",
                "required_evidence": ["complaint_procedure", "complaint_records"],
                "doc_patterns": ["complaint*", "customer_feedback*"],
                "keywords": ["complaint", "customer feedback", "MDR"]
            }
        }
    }
}


def search_documentation(project_dir: Path, patterns: List[str], keywords: List[str]) -> Dict:
    """Search for documentation matching patterns and keywords."""
    result = {
        "documents_found": [],
        "keyword_matches": [],
        "evidence_strength": "none"
    }

    # Common documentation directories
    doc_dirs = [
        project_dir / "qms",
        project_dir / "quality",
        project_dir / "docs",
        project_dir / "documentation",
        project_dir / "procedures",
        project_dir / "sops",
        project_dir / "dhf",
        project_dir / "dmr",
        project_dir
    ]

    # Search for document patterns
    for doc_dir in doc_dirs:
        if not doc_dir.exists():
            continue

        for pattern in patterns:
            for ext in ["*.md", "*.pdf", "*.docx", "*.doc", "*.txt"]:
                full_pattern = f"**/{pattern}{ext}" if not pattern.endswith("*") else f"**/{pattern[:-1]}{ext}"
                try:
                    matches = list(doc_dir.glob(full_pattern))
                    for match in matches:
                        rel_path = str(match.relative_to(project_dir))
                        if rel_path not in result["documents_found"]:
                            result["documents_found"].append(rel_path)
                except Exception:
                    continue

    # Search for keywords in markdown and text files
    for doc_dir in doc_dirs:
        if not doc_dir.exists():
            continue

        for ext in ["*.md", "*.txt"]:
            try:
                for file_path in doc_dir.glob(f"**/{ext}"):
                    try:
                        content = file_path.read_text(encoding='utf-8', errors='ignore').lower()
                        for keyword in keywords:
                            if keyword.lower() in content:
                                rel_path = str(file_path.relative_to(project_dir))
                                if rel_path not in result["keyword_matches"]:
                                    result["keyword_matches"].append(rel_path)
                    except Exception:
                        continue
            except Exception:
                continue

    # Determine evidence strength
    if result["documents_found"] and result["keyword_matches"]:
        result["evidence_strength"] = "strong"
    elif result["documents_found"] or result["keyword_matches"]:
        result["evidence_strength"] = "partial"
    else:
        result["evidence_strength"] = "none"

    return result


def assess_section(project_dir: Path, section_id: str, section_data: Dict) -> Dict:
    """Assess compliance for a QSR section."""
    result = {
        "section": section_id,
        "title": section_data["title"],
        "subsections": [],
        "compliance_score": 0,
        "total_subsections": len(section_data["subsections"]),
        "compliant_subsections": 0
    }

    for subsection_id, subsection_data in section_data["subsections"].items():
        evidence = search_documentation(
            project_dir,
            subsection_data["doc_patterns"],
            subsection_data["keywords"]
        )

        subsection_result = {
            "subsection": subsection_id,
            "title": subsection_data["title"],
            "required_evidence": subsection_data["required_evidence"],
            "evidence_found": evidence,
            "status": "gap" if evidence["evidence_strength"] == "none" else (
                "partial" if evidence["evidence_strength"] == "partial" else "compliant"
            )
        }

        if subsection_result["status"] == "compliant":
            result["compliant_subsections"] += 1
        elif subsection_result["status"] == "partial":
            result["compliant_subsections"] += 0.5

        result["subsections"].append(subsection_result)

    if result["total_subsections"] > 0:
        result["compliance_score"] = round(
            (result["compliant_subsections"] / result["total_subsections"]) * 100, 1
        )

    return result


def generate_gap_report(assessment_results: List[Dict]) -> Dict:
    """Generate gap analysis report."""
    gaps = []
    recommendations = []

    for section in assessment_results:
        for subsection in section["subsections"]:
            if subsection["status"] != "compliant":
                gap = {
                    "section": subsection["subsection"],
                    "title": subsection["title"],
                    "status": subsection["status"],
                    "missing_evidence": subsection["required_evidence"]
                }
                gaps.append(gap)

                if subsection["status"] == "gap":
                    recommendations.append(
                        f"{subsection['subsection']}: Create documentation for {subsection['title']}"
                    )
                else:
                    recommendations.append(
                        f"{subsection['subsection']}: Enhance documentation for {subsection['title']}"
                    )

    return {
        "total_gaps": len([g for g in gaps if g["status"] == "gap"]),
        "total_partial": len([g for g in gaps if g["status"] == "partial"]),
        "gaps": gaps,
        "priority_recommendations": recommendations[:10]  # Top 10
    }


def calculate_overall_compliance(assessment_results: List[Dict]) -> Dict:
    """Calculate overall QSR compliance score."""
    total_subsections = 0
    compliant_subsections = 0

    section_scores = {}
    for section in assessment_results:
        total_subsections += section["total_subsections"]
        compliant_subsections += section["compliant_subsections"]
        section_scores[section["section"]] = section["compliance_score"]

    overall_score = round((compliant_subsections / total_subsections) * 100, 1) if total_subsections > 0 else 0

    # Determine compliance level
    if overall_score >= 90:
        level = "HIGH"
        color = "green"
    elif overall_score >= 70:
        level = "MEDIUM"
        color = "yellow"
    elif overall_score >= 50:
        level = "LOW"
        color = "orange"
    else:
        level = "CRITICAL"
        color = "red"

    return {
        "overall_score": overall_score,
        "compliance_level": level,
        "total_subsections": total_subsections,
        "compliant_subsections": compliant_subsections,
        "section_scores": section_scores
    }


def print_text_report(result: Dict) -> None:
    """Print human-readable compliance report."""
    print("=" * 70)
    print("QMS DOCUMENTATION ASSESSMENT")
    print("(legacy-QSR checklist mapped to ISO 13485:2016 under the QMSR)")
    print("=" * 70)
    print("NOTE: Section numbers are the HISTORICAL pre-2026 QSR structure,")
    print("retained as checklist keys only. Since 2026-02-02 the QMSR (89 FR")
    print("7496) incorporates ISO 13485:2016 by reference into 21 CFR 820;")
    print("the ISO 13485 clause shown per section is the current authority.")

    # Overall compliance
    overall = result["overall_compliance"]
    print(f"\nOVERALL COMPLIANCE: {overall['overall_score']}% ({overall['compliance_level']})")
    print(f"Subsections Assessed: {overall['total_subsections']}")
    print(f"Compliant/Partial: {overall['compliant_subsections']}")

    # Section summary
    print("\n--- SECTION SCORES (legacy QSR key -> current ISO 13485 authority) ---")
    for section in result["assessment"]:
        status = "OK" if section["compliance_score"] >= 70 else "GAP"
        iso_ref = QSR_TO_ISO13485.get(section["section"], "see ISO 13485:2016")
        print(f"  {section['section']} {section['title']} [{iso_ref}]: {section['compliance_score']}% [{status}]")

    # Gap analysis
    gap_report = result["gap_report"]
    print(f"\n--- GAP ANALYSIS ---")
    print(f"Critical Gaps: {gap_report['total_gaps']}")
    print(f"Partial Compliance: {gap_report['total_partial']}")

    if gap_report["gaps"]:
        print("\n  Gaps Identified:")
        for gap in gap_report["gaps"][:15]:  # Show top 15
            status = "GAP" if gap["status"] == "gap" else "PARTIAL"
            print(f"    [{status}] {gap['section']}: {gap['title']}")

    # Recommendations
    if gap_report["priority_recommendations"]:
        print("\n--- PRIORITY RECOMMENDATIONS ---")
        for i, rec in enumerate(gap_report["priority_recommendations"], 1):
            print(f"  {i}. {rec}")

    print("\n" + "=" * 70)
    print(f"Assessment Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description=(
            "QMS Documentation Checker — assesses documentation against the legacy "
            "QSR checklist mapped to ISO 13485:2016, the current authority under "
            "FDA's QMSR (21 CFR 820 as amended effective 2026-02-02). Legacy "
            "820.x section numbers are historical checklist keys, not current law."
        )
    )
    parser.add_argument(
        "project_dir",
        nargs="?",
        default=".",
        help="Project directory to analyze (default: current directory)"
    )
    parser.add_argument(
        "--section",
        help="Analyze one legacy-QSR checklist section only (e.g., 820.30 -> ISO 13485 §7.3 under QMSR)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--detailed",
        action="store_true",
        help="Include detailed evidence in output"
    )

    args = parser.parse_args()
    project_dir = Path(args.project_dir).resolve()

    if not project_dir.exists():
        print(f"Error: Directory not found: {project_dir}", file=sys.stderr)
        sys.exit(1)

    # Filter sections if specific one requested
    sections_to_assess = QSR_REQUIREMENTS
    if args.section:
        if args.section in QSR_REQUIREMENTS:
            sections_to_assess = {args.section: QSR_REQUIREMENTS[args.section]}
        else:
            print(f"Error: Unknown section: {args.section}", file=sys.stderr)
            print(f"Available sections: {', '.join(QSR_REQUIREMENTS.keys())}")
            sys.exit(1)

    # Perform assessment
    assessment_results = []
    for section_id, section_data in sections_to_assess.items():
        section_result = assess_section(project_dir, section_id, section_data)
        assessment_results.append(section_result)

    # Generate reports
    overall_compliance = calculate_overall_compliance(assessment_results)
    gap_report = generate_gap_report(assessment_results)

    result = {
        "project_dir": str(project_dir),
        "assessment_date": datetime.now().isoformat(),
        "regulatory_basis": (
            "Legacy-QSR checklist keys (historical, pre-2026) mapped to ISO 13485:2016, "
            "incorporated by reference into 21 CFR 820 by the QMSR effective 2026-02-02"
        ),
        "overall_compliance": overall_compliance,
        "assessment": assessment_results if args.detailed else [
            {
                "section": s["section"],
                "title": s["title"],
                "compliance_score": s["compliance_score"],
                "status": "compliant" if s["compliance_score"] >= 70 else "gap"
            }
            for s in assessment_results
        ],
        "gap_report": gap_report
    }

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_text_report(result)


if __name__ == "__main__":
    main()
