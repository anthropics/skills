#!/usr/bin/env python3
"""
Data Subject Rights Tracker

Tracks and manages data subject rights requests under GDPR Articles 15-22.
Monitors deadlines, generates response templates, and produces compliance reports.

Usage:
    python data_subject_rights_tracker.py list
    python data_subject_rights_tracker.py add --type access --subject "John Doe"
    python data_subject_rights_tracker.py status --id REQ-001
    python data_subject_rights_tracker.py report --output compliance_report.json
"""

import argparse
import json
import os
import sys
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional
from uuid import uuid4


def add_months(dt: datetime, months: int) -> datetime:
    """Add calendar months per GDPR Art. 12(3) (one month, not 30 days).

    If the target month has no equivalent day (e.g., Jan 31 + 1 month),
    clamp to the last day of the target month.
    """
    month_index = dt.month - 1 + months
    year = dt.year + month_index // 12
    month = month_index % 12 + 1
    # last day of target month
    if month == 12:
        next_month_first = datetime(year + 1, 1, 1)
    else:
        next_month_first = datetime(year, month + 1, 1)
    last_day = (next_month_first - timedelta(days=1)).day
    return dt.replace(year=year, month=month, day=min(dt.day, last_day))


# GDPR Articles for each right
RIGHTS_TYPES = {
    "access": {
        "article": "Art. 15",
        "name": "Right of Access",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to obtain confirmation of processing and access to their data",
        "response_includes": [
            "Purposes of processing",
            "Categories of personal data",
            "Recipients or categories of recipients",
            "Retention period or criteria",
            "Right to lodge complaint",
            "Source of data (if not collected from subject)",
            "Existence of automated decision-making"
        ]
    },
    "rectification": {
        "article": "Art. 16",
        "name": "Right to Rectification",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to have inaccurate personal data corrected",
        "response_includes": [
            "Confirmation of correction",
            "Details of corrected data",
            "Notification to recipients"
        ]
    },
    "erasure": {
        "article": "Art. 17",
        "name": "Right to Erasure (Right to be Forgotten)",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to have their personal data erased",
        "grounds": [
            "Data no longer necessary for original purpose",
            "Consent withdrawn",
            "Objection to processing (no overriding grounds)",
            "Unlawful processing",
            "Legal obligation to erase",
            "Data collected from child"
        ],
        "exceptions": [
            "Freedom of expression",
            "Legal obligation to retain",
            "Public health reasons",
            "Archiving in public interest",
            "Legal claims"
        ]
    },
    "restriction": {
        "article": "Art. 18",
        "name": "Right to Restriction of Processing",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to restrict processing of their data",
        "grounds": [
            "Accuracy contested (during verification)",
            "Processing is unlawful (erasure opposed)",
            "Controller no longer needs data (subject needs for legal claims)",
            "Objection pending verification"
        ]
    },
    "portability": {
        "article": "Art. 20",
        "name": "Right to Data Portability",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to receive their data in a portable format",
        "conditions": [
            "Processing based on consent or contract",
            "Processing carried out by automated means"
        ],
        "format_requirements": [
            "Structured format",
            "Commonly used format",
            "Machine-readable format"
        ]
    },
    "objection": {
        "article": "Art. 21",
        "name": "Right to Object",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right to object to processing",
        "applies_to": [
            "Processing based on legitimate interests",
            "Processing for direct marketing",
            "Processing for research/statistics"
        ]
    },
    "automated": {
        "article": "Art. 22",
        "name": "Rights Related to Automated Decision-Making",
        "deadline_months": 1,  # Art. 12(3): one month of receipt
        "description": "Data subject has the right not to be subject to solely automated decisions",
        "includes": [
            "Right to human intervention",
            "Right to express point of view",
            "Right to contest decision"
        ]
    }
}

# Request statuses
STATUSES = {
    "received": "Request received, pending identity verification",
    "verified": "Identity verified, processing request",
    "in_progress": "Gathering data / processing request",
    "pending_info": "Awaiting additional information from subject",
    "extended": "Deadline extended (complex request)",
    "completed": "Request completed and response sent",
    "refused": "Request refused (with justification)",
    "escalated": "Escalated to DPO/legal"
}


class RightsTracker:
    """Manages data subject rights requests."""

    def __init__(self, data_file: str = "dsr_requests.json"):
        self.data_file = Path(data_file)
        self.requests = self._load_requests()

    def _load_requests(self) -> Dict:
        """Load requests from file."""
        if self.data_file.exists():
            with open(self.data_file, "r") as f:
                return json.load(f)
        return {"requests": [], "metadata": {"created": datetime.now().isoformat()}}

    def _save_requests(self):
        """Save requests to file."""
        self.requests["metadata"]["updated"] = datetime.now().isoformat()
        with open(self.data_file, "w") as f:
            json.dump(self.requests, f, indent=2)

    def _generate_id(self) -> str:
        """Generate unique request ID."""
        count = len(self.requests["requests"]) + 1
        return f"DSR-{datetime.now().strftime('%Y%m')}-{count:04d}"

    def add_request(
        self,
        right_type: str,
        subject_name: str,
        subject_email: str,
        details: str = ""
    ) -> Dict:
        """Add a new data subject request."""
        if right_type not in RIGHTS_TYPES:
            raise ValueError(f"Invalid right type. Must be one of: {list(RIGHTS_TYPES.keys())}")

        right_info = RIGHTS_TYPES[right_type]
        now = datetime.now()
        # Art. 12(3): respond within one calendar month of receipt
        deadline = add_months(now, right_info["deadline_months"])

        request = {
            "id": self._generate_id(),
            "type": right_type,
            "article": right_info["article"],
            "right_name": right_info["name"],
            "subject": {
                "name": subject_name,
                "email": subject_email,
                "verified": False
            },
            "details": details,
            "status": "received",
            "status_description": STATUSES["received"],
            "dates": {
                "received": now.isoformat(),
                "deadline": deadline.isoformat(),
                "verified": None,
                "completed": None
            },
            "notes": [],
            "response": None
        }

        self.requests["requests"].append(request)
        self._save_requests()
        return request

    def update_status(
        self,
        request_id: str,
        new_status: str,
        note: str = ""
    ) -> Optional[Dict]:
        """Update request status."""
        if new_status not in STATUSES:
            raise ValueError(f"Invalid status. Must be one of: {list(STATUSES.keys())}")

        for req in self.requests["requests"]:
            if req["id"] == request_id:
                req["status"] = new_status
                req["status_description"] = STATUSES[new_status]

                if new_status == "verified":
                    req["subject"]["verified"] = True
                    req["dates"]["verified"] = datetime.now().isoformat()
                elif new_status == "completed":
                    req["dates"]["completed"] = datetime.now().isoformat()
                elif new_status == "extended":
                    # Art. 12(3): extendable by two further calendar months for
                    # complex/numerous requests (data subject informed within month 1)
                    original_deadline = datetime.fromisoformat(req["dates"]["deadline"])
                    req["dates"]["deadline"] = add_months(original_deadline, 2).isoformat()

                if note:
                    req["notes"].append({
                        "timestamp": datetime.now().isoformat(),
                        "note": note
                    })

                self._save_requests()
                return req

        return None

    def get_request(self, request_id: str) -> Optional[Dict]:
        """Get request by ID."""
        for req in self.requests["requests"]:
            if req["id"] == request_id:
                return req
        return None

    def list_requests(
        self,
        status_filter: Optional[str] = None,
        overdue_only: bool = False
    ) -> List[Dict]:
        """List requests with optional filtering."""
        results = []
        now = datetime.now()

        for req in self.requests["requests"]:
            if status_filter and req["status"] != status_filter:
                continue

            deadline = datetime.fromisoformat(req["dates"]["deadline"])
            is_overdue = deadline < now and req["status"] not in ["completed", "refused"]

            if overdue_only and not is_overdue:
                continue

            req_summary = {
                **req,
                "is_overdue": is_overdue,
                "days_remaining": (deadline - now).days if not is_overdue else 0
            }
            results.append(req_summary)

        return results

    def generate_report(self) -> Dict:
        """Generate compliance report."""
        now = datetime.now()
        total = len(self.requests["requests"])

        status_counts = {}
        for status in STATUSES:
            status_counts[status] = sum(1 for r in self.requests["requests"] if r["status"] == status)

        type_counts = {}
        for right_type in RIGHTS_TYPES:
            type_counts[right_type] = sum(1 for r in self.requests["requests"] if r["type"] == right_type)

        overdue = []
        completed_on_time = 0
        completed_late = 0

        for req in self.requests["requests"]:
            deadline = datetime.fromisoformat(req["dates"]["deadline"])

            if req["status"] in ["completed", "refused"]:
                completed_date = datetime.fromisoformat(req["dates"]["completed"])
                if completed_date <= deadline:
                    completed_on_time += 1
                else:
                    completed_late += 1
            elif deadline < now:
                overdue.append({
                    "id": req["id"],
                    "type": req["type"],
                    "subject": req["subject"]["name"],
                    "days_overdue": (now - deadline).days
                })

        compliance_rate = (completed_on_time / (completed_on_time + completed_late) * 100) if (completed_on_time + completed_late) > 0 else 100

        return {
            "report_date": now.isoformat(),
            "summary": {
                "total_requests": total,
                "open_requests": total - status_counts.get("completed", 0) - status_counts.get("refused", 0),
                "overdue_requests": len(overdue),
                "compliance_rate": round(compliance_rate, 1)
            },
            "by_status": status_counts,
            "by_type": type_counts,
            "overdue_details": overdue,
            "performance": {
                "completed_on_time": completed_on_time,
                "completed_late": completed_late,
                "average_response_days": self._calculate_avg_response_time()
            }
        }

    def _calculate_avg_response_time(self) -> float:
        """Calculate average response time for completed requests."""
        response_times = []

        for req in self.requests["requests"]:
            if req["status"] == "completed" and req["dates"]["completed"]:
                received = datetime.fromisoformat(req["dates"]["received"])
                completed = datetime.fromisoformat(req["dates"]["completed"])
                response_times.append((completed - received).days)

        return round(sum(response_times) / len(response_times), 1) if response_times else 0

    def generate_response_template(self, request_id: str) -> Optional[str]:
        """Generate response template for a request."""
        req = self.get_request(request_id)
        if not req:
            return None

        right_info = RIGHTS_TYPES.get(req["type"], {})
        template = f"""
Subject: Response to Your {right_info.get('name', 'Data Subject')} Request ({req['id']})

Dear {req['subject']['name']},

Thank you for your request dated {req['dates']['received'][:10]} exercising your {right_info.get('name', 'data protection right')} under {right_info.get('article', 'GDPR')}.

We have processed your request and respond as follows:

[RESPONSE DETAILS HERE]

"""
        if req["type"] == "access":
            template += """
As required under Article 15, we provide the following information:

1. Purposes of Processing:
   [List purposes]

2. Categories of Personal Data:
   [List categories]

3. Recipients:
   [List recipients or categories]

4. Retention Period:
   [Specify period or criteria]

5. Your Rights:
   - Right to rectification (Art. 16)
   - Right to erasure (Art. 17)
   - Right to restriction (Art. 18)
   - Right to object (Art. 21)
   - Right to lodge complaint with supervisory authority

6. Source of Data:
   [Specify if not collected from you directly]

7. Automated Decision-Making:
   [Confirm if applicable and provide meaningful information]

Enclosed: Copy of your personal data
"""
        elif req["type"] == "erasure":
            template += """
We confirm that your personal data has been erased from our systems, except where:
- We are legally required to retain it
- It is necessary for legal claims
- [Other applicable exceptions]

We have also notified the following recipients of the erasure:
[List recipients]
"""
        elif req["type"] == "portability":
            template += """
Please find attached your personal data in [JSON/CSV] format.

This includes all data:
- Provided by you
- Processed based on your consent or contract
- Processed by automated means

You may transmit this data to another controller or request direct transmission where technically feasible.
"""

        template += f"""
If you have any questions about this response, please contact our Data Protection Officer at [DPO EMAIL].

If you are not satisfied with our response, you have the right to lodge a complaint with the supervisory authority:
[SUPERVISORY AUTHORITY DETAILS]

Yours sincerely,
[CONTROLLER NAME]
Data Protection Team

Reference: {req['id']}
"""
        return template


def main():
    parser = argparse.ArgumentParser(
        description="Track and manage data subject rights requests"
    )
    parser.add_argument(
        "--data-file",
        default="dsr_requests.json",
        help="Path to requests data file (default: dsr_requests.json)"
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Add command
    add_parser = subparsers.add_parser("add", help="Add new request")
    add_parser.add_argument("--type", "-t", required=True, choices=RIGHTS_TYPES.keys())
    add_parser.add_argument("--subject", "-s", required=True, help="Subject name")
    add_parser.add_argument("--email", "-e", required=True, help="Subject email")
    add_parser.add_argument("--details", "-d", default="", help="Request details")

    # List command
    list_parser = subparsers.add_parser("list", help="List requests")
    list_parser.add_argument("--status", choices=STATUSES.keys(), help="Filter by status")
    list_parser.add_argument("--overdue", action="store_true", help="Show only overdue")
    list_parser.add_argument("--json", action="store_true", help="JSON output")

    # Status command
    status_parser = subparsers.add_parser("status", help="Get/update request status")
    status_parser.add_argument("--id", required=True, help="Request ID")
    status_parser.add_argument("--update", choices=STATUSES.keys(), help="Update status")
    status_parser.add_argument("--note", default="", help="Add note")

    # Report command
    report_parser = subparsers.add_parser("report", help="Generate compliance report")
    report_parser.add_argument("--output", "-o", help="Output file")

    # Template command
    template_parser = subparsers.add_parser("template", help="Generate response template")
    template_parser.add_argument("--id", required=True, help="Request ID")

    # Types command
    subparsers.add_parser("types", help="List available request types")

    args = parser.parse_args()

    tracker = RightsTracker(args.data_file)

    if args.command == "add":
        request = tracker.add_request(
            args.type, args.subject, args.email, args.details
        )
        print(f"Request created: {request['id']}")
        print(f"Type: {request['right_name']} ({request['article']})")
        print(f"Deadline: {request['dates']['deadline'][:10]}")

    elif args.command == "list":
        requests = tracker.list_requests(args.status, args.overdue)
        if args.json:
            print(json.dumps(requests, indent=2))
        else:
            if not requests:
                print("No requests found.")
                return
            print(f"{'ID':<20} {'Type':<15} {'Subject':<20} {'Status':<15} {'Deadline':<12} {'Overdue'}")
            print("-" * 95)
            for req in requests:
                overdue_flag = "YES" if req.get("is_overdue") else ""
                print(f"{req['id']:<20} {req['type']:<15} {req['subject']['name'][:20]:<20} {req['status']:<15} {req['dates']['deadline'][:10]:<12} {overdue_flag}")

    elif args.command == "status":
        if args.update:
            req = tracker.update_status(args.id, args.update, args.note)
            if req:
                print(f"Updated {args.id} to status: {args.update}")
            else:
                print(f"Request not found: {args.id}")
        else:
            req = tracker.get_request(args.id)
            if req:
                print(json.dumps(req, indent=2))
            else:
                print(f"Request not found: {args.id}")

    elif args.command == "report":
        report = tracker.generate_report()
        output = json.dumps(report, indent=2)
        if args.output:
            with open(args.output, "w") as f:
                f.write(output)
            print(f"Report written to {args.output}")
        else:
            print(output)

    elif args.command == "template":
        template = tracker.generate_response_template(args.id)
        if template:
            print(template)
        else:
            print(f"Request not found: {args.id}")

    elif args.command == "types":
        print("Available Request Types:")
        print("-" * 60)
        for key, info in RIGHTS_TYPES.items():
            print(f"\n{key} ({info['article']})")
            print(f"  {info['name']}")
            print(f"  Deadline: {info['deadline_months']} calendar month(s) (Art. 12(3))")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
