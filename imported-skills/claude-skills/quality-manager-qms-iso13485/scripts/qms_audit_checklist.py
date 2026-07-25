#!/usr/bin/env python3
"""
QMS Internal Audit Checklist Generator

Generates audit checklists for ISO 13485:2016 clauses and QMS processes.
Supports process audits, system audits, and clause-specific audits.

Usage:
    python qms_audit_checklist.py --clause 7.3
    python qms_audit_checklist.py --process design-control
    python qms_audit_checklist.py --audit-type system --output json
    python qms_audit_checklist.py --interactive
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Optional


# ISO 13485:2016 Clause Structure with Audit Questions
ISO13485_CLAUSES = {
    "4.1": {
        "title": "General Requirements",
        "questions": [
            "Are QMS processes identified and documented?",
            "Is the sequence and interaction of processes defined?",
            "Are criteria and methods for process operation determined?",
            "Are resources and information available for process operation?",
            "Are processes monitored, measured, and analyzed?",
            "Are actions taken to achieve planned results?",
            "Is outsourced process control documented?",
            "Are changes to processes managed?"
        ]
    },
    "4.2.1": {
        "title": "Documentation Requirements - General",
        "questions": [
            "Is a quality policy documented?",
            "Are quality objectives documented?",
            "Is a quality manual maintained?",
            "Are required documented procedures established?",
            "Are documents needed for process planning and operation maintained?",
            "Are required records maintained?",
            "Is a medical device file established for each device type?"
        ]
    },
    "4.2.2": {
        "title": "Quality Manual",
        "questions": [
            "Does the quality manual include QMS scope?",
            "Are exclusions justified?",
            "Are documented procedures included or referenced?",
            "Is the interaction between processes described?",
            "Is the quality manual controlled?"
        ]
    },
    "4.2.3": {
        "title": "Control of Documents",
        "questions": [
            "Are documents approved before issue?",
            "Are documents reviewed and updated as necessary?",
            "Are changes and revision status identified?",
            "Are current versions available at points of use?",
            "Are documents legible and identifiable?",
            "Are external documents identified and controlled?",
            "Is unintended use of obsolete documents prevented?",
            "Is there a document change control process?"
        ]
    },
    "4.2.4": {
        "title": "Control of Records",
        "questions": [
            "Is there a procedure for record control?",
            "Are records legible and identifiable?",
            "Are records retrievable?",
            "Are retention times defined?",
            "Is protection from damage ensured?",
            "Are confidential records protected?",
            "Is record disposal controlled?"
        ]
    },
    "5.1": {
        "title": "Management Commitment",
        "questions": [
            "Is there evidence of management commitment to QMS?",
            "Is the importance of regulatory requirements communicated?",
            "Is a quality policy established?",
            "Are quality objectives established?",
            "Are management reviews conducted?",
            "Are resources provided for QMS?"
        ]
    },
    "5.2": {
        "title": "Customer Focus",
        "questions": [
            "Are customer requirements determined?",
            "Are applicable regulatory requirements determined?",
            "Are customer and regulatory requirements met?",
            "Is customer satisfaction enhanced?"
        ]
    },
    "5.3": {
        "title": "Quality Policy",
        "questions": [
            "Is the quality policy appropriate to the organization?",
            "Does it include commitment to compliance?",
            "Does it include commitment to effectiveness?",
            "Does it provide framework for quality objectives?",
            "Is it communicated and understood?",
            "Is it reviewed for continuing suitability?"
        ]
    },
    "5.4.1": {
        "title": "Quality Objectives",
        "questions": [
            "Are quality objectives measurable?",
            "Are they consistent with quality policy?",
            "Are they established at relevant functions?",
            "Do they include product requirements?",
            "Do they include compliance requirements?"
        ]
    },
    "5.4.2": {
        "title": "QMS Planning",
        "questions": [
            "Is QMS planning carried out to meet requirements?",
            "Is QMS planning done to meet quality objectives?",
            "Is QMS integrity maintained during changes?"
        ]
    },
    "5.5.1": {
        "title": "Responsibility and Authority",
        "questions": [
            "Are responsibilities and authorities defined?",
            "Are they documented?",
            "Are they communicated?",
            "Are interrelationships defined?"
        ]
    },
    "5.5.2": {
        "title": "Management Representative",
        "questions": [
            "Is a management representative appointed?",
            "Is authority to ensure QMS processes established?",
            "Is authority to report to top management defined?",
            "Is authority to promote awareness of requirements defined?"
        ]
    },
    "5.5.3": {
        "title": "Internal Communication",
        "questions": [
            "Are communication processes established?",
            "Is QMS effectiveness communicated?",
            "Is information communicated appropriately?"
        ]
    },
    "5.6": {
        "title": "Management Review",
        "questions": [
            "Are management reviews planned?",
            "Are all required inputs reviewed?",
            "Are outputs documented?",
            "Are action items followed up?",
            "Are records maintained?"
        ]
    },
    "6.1": {
        "title": "Provision of Resources",
        "questions": [
            "Are resources determined?",
            "Are resources provided for QMS?",
            "Are resources provided for customer satisfaction?",
            "Are resources provided for regulatory compliance?"
        ]
    },
    "6.2": {
        "title": "Human Resources",
        "questions": [
            "Is competence defined for personnel?",
            "Is training provided to achieve competence?",
            "Is training effectiveness evaluated?",
            "Is awareness of job relevance ensured?",
            "Are training records maintained?"
        ]
    },
    "6.3": {
        "title": "Infrastructure",
        "questions": [
            "Is necessary infrastructure determined?",
            "Are buildings and workspace adequate?",
            "Is process equipment adequate?",
            "Are supporting services adequate?",
            "Are maintenance requirements documented?"
        ]
    },
    "6.4": {
        "title": "Work Environment",
        "questions": [
            "Is work environment determined?",
            "Are environmental requirements documented?",
            "Is contamination control adequate?",
            "Are personnel health and cleanliness controlled?",
            "Are environmental conditions monitored?"
        ]
    },
    "7.1": {
        "title": "Planning of Product Realization",
        "questions": [
            "Are quality objectives for product defined?",
            "Are processes needed determined?",
            "Is verification and validation defined?",
            "Are records requirements defined?",
            "Is risk management applied?"
        ]
    },
    "7.2": {
        "title": "Customer-Related Processes",
        "questions": [
            "Are customer requirements determined?",
            "Are regulatory requirements determined?",
            "Are requirements reviewed before commitment?",
            "Are differences resolved before acceptance?",
            "Is communication with customers effective?"
        ]
    },
    "7.3.1": {
        "title": "Design and Development Planning",
        "questions": [
            "Are design stages determined?",
            "Are review activities defined?",
            "Are verification activities defined?",
            "Are validation activities defined?",
            "Are responsibilities assigned?",
            "Are interfaces managed?"
        ]
    },
    "7.3.2": {
        "title": "Design and Development Inputs",
        "questions": [
            "Are functional requirements defined?",
            "Are performance requirements defined?",
            "Are safety requirements defined?",
            "Are regulatory requirements identified?",
            "Are previous design inputs considered?",
            "Are risk management outputs included?"
        ]
    },
    "7.3.3": {
        "title": "Design and Development Outputs",
        "questions": [
            "Do outputs meet input requirements?",
            "Is purchasing information provided?",
            "Are acceptance criteria defined?",
            "Are essential characteristics specified?",
            "Are outputs approved before release?"
        ]
    },
    "7.3.4": {
        "title": "Design and Development Review",
        "questions": [
            "Are design reviews conducted at suitable stages?",
            "Is ability to meet requirements evaluated?",
            "Are problems identified?",
            "Are follow-up actions recorded?",
            "Are appropriate functions represented?"
        ]
    },
    "7.3.5": {
        "title": "Design and Development Verification",
        "questions": [
            "Is verification performed per plan?",
            "Do outputs meet inputs?",
            "Are verification records maintained?",
            "Are verification methods appropriate?"
        ]
    },
    "7.3.6": {
        "title": "Design and Development Validation",
        "questions": [
            "Is validation performed per plan?",
            "Is product evaluated for intended use?",
            "Is clinical evaluation included?",
            "Are validation records maintained?",
            "Is validation completed before product delivery?"
        ]
    },
    "7.3.7": {
        "title": "Design and Development Transfer",
        "questions": [
            "Are outputs verified before transfer?",
            "Is manufacturing capability verified?",
            "Are transfer activities documented?"
        ]
    },
    "7.3.8": {
        "title": "Control of Design and Development Changes",
        "questions": [
            "Are design changes identified?",
            "Are changes reviewed?",
            "Are changes verified?",
            "Are changes validated as appropriate?",
            "Is impact on product assessed?",
            "Are changes approved before implementation?"
        ]
    },
    "7.4.1": {
        "title": "Purchasing Process",
        "questions": [
            "Are suppliers evaluated and selected?",
            "Are evaluation criteria established?",
            "Is supplier performance monitored?",
            "Are re-evaluation criteria defined?",
            "Is purchased product verified?"
        ]
    },
    "7.4.2": {
        "title": "Purchasing Information",
        "questions": [
            "Is purchasing information adequate?",
            "Are product requirements specified?",
            "Are QMS requirements specified?",
            "Are personnel requirements specified?"
        ]
    },
    "7.4.3": {
        "title": "Verification of Purchased Product",
        "questions": [
            "Is incoming inspection adequate?",
            "Are verification activities defined?",
            "Are verification records maintained?",
            "Is source verification defined if applicable?"
        ]
    },
    "7.5.1": {
        "title": "Control of Production and Service Provision",
        "questions": [
            "Is product information available?",
            "Are work instructions available?",
            "Is suitable equipment used?",
            "Are monitoring devices available?",
            "Is monitoring implemented?",
            "Are release activities defined?",
            "Are labeling requirements met?"
        ]
    },
    "7.5.2": {
        "title": "Cleanliness of Product",
        "questions": [
            "Are cleanliness requirements documented?",
            "Is contamination controlled?",
            "Are process agents controlled?"
        ]
    },
    "7.5.3": {
        "title": "Installation Activities",
        "questions": [
            "Are installation requirements documented?",
            "Are acceptance criteria defined?",
            "Are installation records maintained?"
        ]
    },
    "7.5.4": {
        "title": "Servicing Activities",
        "questions": [
            "Are servicing procedures documented?",
            "Are reference materials controlled?",
            "Are service records maintained?",
            "Is feedback analyzed?"
        ]
    },
    "7.5.5": {
        "title": "Sterile Medical Devices",
        "questions": [
            "Is sterilization validated?",
            "Are process parameters controlled?",
            "Is sterile barrier validated?",
            "Are sterilization records maintained?"
        ]
    },
    "7.5.6": {
        "title": "Validation of Processes",
        "questions": [
            "Are special processes identified?",
            "Are validation procedures documented?",
            "Is equipment qualified?",
            "Are personnel qualified?",
            "Are validation records maintained?",
            "Are revalidation criteria defined?"
        ]
    },
    "7.5.7": {
        "title": "Particular Requirements for Validation",
        "questions": [
            "Are validation methods defined?",
            "Are acceptance criteria established?",
            "Is software validation appropriate?",
            "Are validation records maintained?"
        ]
    },
    "7.5.8": {
        "title": "Identification",
        "questions": [
            "Is product identified throughout realization?",
            "Is documentation identified?",
            "Is UDI implemented as required?"
        ]
    },
    "7.5.9": {
        "title": "Traceability",
        "questions": [
            "Are traceability procedures documented?",
            "Are components traceable?",
            "Is work environment recorded?",
            "Is distribution recorded?",
            "Is traceability extent defined?"
        ]
    },
    "7.5.10": {
        "title": "Customer Property",
        "questions": [
            "Is customer property identified?",
            "Is it verified on receipt?",
            "Is it protected and safeguarded?",
            "Is loss or damage reported?"
        ]
    },
    "7.5.11": {
        "title": "Preservation of Product",
        "questions": [
            "Is product identified?",
            "Is handling controlled?",
            "Is packaging controlled?",
            "Is storage controlled?",
            "Is protection adequate?"
        ]
    },
    "7.6": {
        "title": "Control of Monitoring and Measuring Equipment",
        "questions": [
            "Is equipment calibrated?",
            "Is calibration traceable?",
            "Is calibration status identified?",
            "Is equipment protected from damage?",
            "Is software validated?",
            "Are records maintained?"
        ]
    },
    "8.1": {
        "title": "Measurement, Analysis and Improvement - General",
        "questions": [
            "Are monitoring activities planned?",
            "Are analysis activities planned?",
            "Are improvement activities planned?"
        ]
    },
    "8.2.1": {
        "title": "Feedback",
        "questions": [
            "Is feedback collected?",
            "Is feedback analyzed?",
            "Is feedback used for improvement?",
            "Is regulatory feedback included?"
        ]
    },
    "8.2.2": {
        "title": "Complaint Handling",
        "questions": [
            "Is there a complaint procedure?",
            "Are complaints investigated?",
            "Are regulatory reports made if required?",
            "Is trend analysis performed?",
            "Are CAPAs initiated when warranted?"
        ]
    },
    "8.2.3": {
        "title": "Reporting to Regulatory Authorities",
        "questions": [
            "Are reporting requirements identified?",
            "Are reports submitted timely?",
            "Are records maintained?"
        ]
    },
    "8.2.4": {
        "title": "Internal Audit",
        "questions": [
            "Is an audit program established?",
            "Are audit criteria defined?",
            "Are auditors independent?",
            "Are auditors competent?",
            "Are audit records maintained?",
            "Are findings followed up?"
        ]
    },
    "8.2.5": {
        "title": "Monitoring and Measurement of Processes",
        "questions": [
            "Are processes monitored?",
            "Are suitable methods used?",
            "Is process capability demonstrated?",
            "Are corrections made when needed?"
        ]
    },
    "8.2.6": {
        "title": "Monitoring and Measurement of Product",
        "questions": [
            "Is product inspected?",
            "Are acceptance criteria met?",
            "Is release authorized?",
            "Is traceability to inspection recorded?",
            "Are records maintained?"
        ]
    },
    "8.3": {
        "title": "Control of Nonconforming Product",
        "questions": [
            "Is nonconforming product identified?",
            "Is it documented?",
            "Is it evaluated?",
            "Is it segregated?",
            "Is disposition determined?",
            "Is rework verified?",
            "Is concession controlled?",
            "Is post-delivery NC investigated?"
        ]
    },
    "8.4": {
        "title": "Analysis of Data",
        "questions": [
            "Is data collected?",
            "Is feedback analyzed?",
            "Is conformity data analyzed?",
            "Is process data analyzed?",
            "Is supplier data analyzed?",
            "Are audit results analyzed?"
        ]
    },
    "8.5.1": {
        "title": "Improvement - General",
        "questions": [
            "Is continual improvement pursued?",
            "Are policy, objectives, audits, data, actions, and reviews used?"
        ]
    },
    "8.5.2": {
        "title": "Corrective Action",
        "questions": [
            "Is there a CA procedure?",
            "Are NCs reviewed (including complaints)?",
            "Is root cause determined?",
            "Is action needed evaluated?",
            "Is action determined and implemented?",
            "Are results documented?",
            "Is effectiveness verified?"
        ]
    },
    "8.5.3": {
        "title": "Preventive Action",
        "questions": [
            "Is there a PA procedure?",
            "Are potential NCs identified?",
            "Is action needed evaluated?",
            "Is action determined and implemented?",
            "Are results documented?",
            "Is effectiveness verified?"
        ]
    }
}

# Process-to-Clause Mapping
PROCESS_MAPPING = {
    "document-control": ["4.2.1", "4.2.2", "4.2.3", "4.2.4"],
    "management-review": ["5.6"],
    "internal-audit": ["8.2.4"],
    "training": ["6.2"],
    "design-control": ["7.3.1", "7.3.2", "7.3.3", "7.3.4", "7.3.5", "7.3.6", "7.3.7", "7.3.8"],
    "purchasing": ["7.4.1", "7.4.2", "7.4.3"],
    "production": ["7.5.1", "7.5.2", "7.5.6", "7.5.7", "7.5.8", "7.5.9", "7.5.11"],
    "capa": ["8.5.2", "8.5.3"],
    "nonconformity": ["8.3"],
    "calibration": ["7.6"],
    "complaint-handling": ["8.2.1", "8.2.2", "8.2.3"],
    "risk-management": ["7.1"],
    "infrastructure": ["6.3", "6.4"],
    "customer-requirements": ["5.2", "7.2"]
}


def get_clause_checklist(clause: str) -> dict:
    """Get audit checklist for a specific clause."""
    if clause not in ISO13485_CLAUSES:
        return {"error": f"Clause {clause} not found"}

    clause_data = ISO13485_CLAUSES[clause]
    return {
        "clause": clause,
        "title": clause_data["title"],
        "questions": clause_data["questions"],
        "question_count": len(clause_data["questions"])
    }


def get_process_checklist(process: str) -> dict:
    """Get audit checklist for a specific process."""
    if process not in PROCESS_MAPPING:
        available = ", ".join(sorted(PROCESS_MAPPING.keys()))
        return {"error": f"Process '{process}' not found. Available: {available}"}

    clauses = PROCESS_MAPPING[process]
    questions = []

    for clause in clauses:
        if clause in ISO13485_CLAUSES:
            clause_data = ISO13485_CLAUSES[clause]
            for q in clause_data["questions"]:
                questions.append({
                    "clause": clause,
                    "clause_title": clause_data["title"],
                    "question": q
                })

    return {
        "process": process,
        "clauses_covered": clauses,
        "questions": questions,
        "question_count": len(questions)
    }


def get_system_audit_checklist() -> dict:
    """Get complete system audit checklist covering all clauses."""
    all_questions = []

    for clause, data in sorted(ISO13485_CLAUSES.items()):
        for q in data["questions"]:
            all_questions.append({
                "clause": clause,
                "clause_title": data["title"],
                "question": q
            })

    return {
        "audit_type": "system",
        "clauses_covered": list(ISO13485_CLAUSES.keys()),
        "questions": all_questions,
        "question_count": len(all_questions)
    }


def format_checklist_text(checklist: dict) -> str:
    """Format checklist for text output."""
    lines = []

    if "error" in checklist:
        return f"Error: {checklist['error']}"

    lines.append("=" * 70)
    lines.append("ISO 13485:2016 INTERNAL AUDIT CHECKLIST")
    lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    lines.append("=" * 70)

    if "clause" in checklist:
        lines.append(f"\nClause: {checklist['clause']} - {checklist['title']}")
        lines.append("-" * 50)
        for i, q in enumerate(checklist["questions"], 1):
            lines.append(f"\n{i}. {q}")
            lines.append("   [ ] C  [ ] NC  [ ] OBS  [ ] N/A")
            lines.append("   Evidence: _________________________________")
            lines.append("   Notes: ____________________________________")

    elif "process" in checklist:
        lines.append(f"\nProcess: {checklist['process'].replace('-', ' ').title()}")
        lines.append(f"Clauses Covered: {', '.join(checklist['clauses_covered'])}")
        lines.append("-" * 50)

        current_clause = None
        item_num = 1
        for q in checklist["questions"]:
            if q["clause"] != current_clause:
                current_clause = q["clause"]
                lines.append(f"\n--- {q['clause']} {q['clause_title']} ---")

            lines.append(f"\n{item_num}. {q['question']}")
            lines.append("   [ ] C  [ ] NC  [ ] OBS  [ ] N/A")
            lines.append("   Evidence: _________________________________")
            lines.append("   Notes: ____________________________________")
            item_num += 1

    elif "audit_type" in checklist:
        lines.append(f"\nAudit Type: Full System Audit")
        lines.append(f"Total Clauses: {len(checklist['clauses_covered'])}")
        lines.append("-" * 50)

        current_clause = None
        item_num = 1
        for q in checklist["questions"]:
            if q["clause"] != current_clause:
                current_clause = q["clause"]
                lines.append(f"\n{'=' * 40}")
                lines.append(f"CLAUSE {q['clause']}: {q['clause_title']}")
                lines.append("=" * 40)

            lines.append(f"\n{item_num}. {q['question']}")
            lines.append("   [ ] C  [ ] NC  [ ] OBS  [ ] N/A")
            lines.append("   Evidence: _________________________________")
            item_num += 1

    lines.append("\n" + "=" * 70)
    lines.append(f"Total Questions: {checklist['question_count']}")
    lines.append("")
    lines.append("Legend: C=Conforming, NC=Nonconforming, OBS=Observation, N/A=Not Applicable")
    lines.append("=" * 70)

    return "\n".join(lines)


def interactive_mode():
    """Run interactive audit checklist generator."""
    print("\n" + "=" * 50)
    print("QMS INTERNAL AUDIT CHECKLIST GENERATOR")
    print("=" * 50)

    print("\nSelect audit type:")
    print("1. Clause-specific audit")
    print("2. Process audit")
    print("3. Full system audit")
    print("4. List available processes")
    print("5. List all clauses")
    print("6. Exit")

    choice = input("\nEnter choice (1-6): ").strip()

    if choice == "1":
        print("\nAvailable clause sections:")
        print("  4.x - Quality Management System")
        print("  5.x - Management Responsibility")
        print("  6.x - Resource Management")
        print("  7.x - Product Realization")
        print("  8.x - Measurement, Analysis, Improvement")

        clause = input("\nEnter clause number (e.g., 7.3.1): ").strip()
        checklist = get_clause_checklist(clause)
        print(format_checklist_text(checklist))

    elif choice == "2":
        processes = sorted(PROCESS_MAPPING.keys())
        print("\nAvailable processes:")
        for i, p in enumerate(processes, 1):
            clauses = PROCESS_MAPPING[p]
            print(f"  {i}. {p} (clauses: {', '.join(clauses)})")

        process = input("\nEnter process name: ").strip().lower()
        checklist = get_process_checklist(process)
        print(format_checklist_text(checklist))

    elif choice == "3":
        print("\nGenerating full system audit checklist...")
        checklist = get_system_audit_checklist()
        print(format_checklist_text(checklist))

    elif choice == "4":
        processes = sorted(PROCESS_MAPPING.keys())
        print("\nAvailable QMS Processes:")
        print("-" * 50)
        for p in processes:
            clauses = PROCESS_MAPPING[p]
            print(f"  {p}")
            print(f"    Clauses: {', '.join(clauses)}")

    elif choice == "5":
        print("\nISO 13485:2016 Clauses:")
        print("-" * 50)
        for clause, data in sorted(ISO13485_CLAUSES.items()):
            print(f"  {clause}: {data['title']} ({len(data['questions'])} questions)")

    elif choice == "6":
        print("Exiting.")
        return

    else:
        print("Invalid choice.")


def main():
    parser = argparse.ArgumentParser(
        description="Generate ISO 13485:2016 internal audit checklists",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python qms_audit_checklist.py --clause 7.3
  python qms_audit_checklist.py --process design-control
  python qms_audit_checklist.py --audit-type system --output json
  python qms_audit_checklist.py --list-processes
  python qms_audit_checklist.py --list-clauses
  python qms_audit_checklist.py --interactive
        """
    )

    parser.add_argument(
        "--clause",
        help="Generate checklist for specific clause (e.g., 7.3.1, 8.5.2)"
    )
    parser.add_argument(
        "--process",
        help="Generate checklist for process (e.g., design-control, capa)"
    )
    parser.add_argument(
        "--audit-type",
        choices=["clause", "process", "system"],
        help="Audit type for checklist generation"
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)"
    )
    parser.add_argument(
        "--list-processes",
        action="store_true",
        help="List available QMS processes"
    )
    parser.add_argument(
        "--list-clauses",
        action="store_true",
        help="List all ISO 13485 clauses"
    )
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run in interactive mode"
    )

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.list_processes:
        processes = sorted(PROCESS_MAPPING.keys())
        if args.output == "json":
            result = {p: PROCESS_MAPPING[p] for p in processes}
            print(json.dumps(result, indent=2))
        else:
            print("\nAvailable QMS Processes:")
            print("-" * 50)
            for p in processes:
                clauses = PROCESS_MAPPING[p]
                print(f"  {p}: {', '.join(clauses)}")
        return

    if args.list_clauses:
        if args.output == "json":
            result = {c: {"title": d["title"], "question_count": len(d["questions"])}
                     for c, d in sorted(ISO13485_CLAUSES.items())}
            print(json.dumps(result, indent=2))
        else:
            print("\nISO 13485:2016 Clauses:")
            print("-" * 50)
            for clause, data in sorted(ISO13485_CLAUSES.items()):
                print(f"  {clause}: {data['title']} ({len(data['questions'])} questions)")
        return

    checklist = None

    if args.clause:
        checklist = get_clause_checklist(args.clause)
    elif args.process:
        checklist = get_process_checklist(args.process)
    elif args.audit_type == "system":
        checklist = get_system_audit_checklist()
    else:
        parser.print_help()
        return

    if checklist:
        if args.output == "json":
            print(json.dumps(checklist, indent=2))
        else:
            print(format_checklist_text(checklist))


if __name__ == "__main__":
    main()
