#!/usr/bin/env python3
"""
Regulatory Submission Tracking System
Automates monitoring and reporting of regulatory submission status
"""

import json
import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict
from enum import Enum

class SubmissionType(Enum):
    FDA_510K = "FDA_510K"
    FDA_PMA = "FDA_PMA"
    FDA_DE_NOVO = "FDA_DE_NOVO"
    EU_MDR_CE = "EU_MDR_CE"
    ISO_CERTIFICATION = "ISO_CERTIFICATION"
    GLOBAL_REGULATORY = "GLOBAL_REGULATORY"

class SubmissionStatus(Enum):
    PLANNING = "PLANNING"
    IN_PREPARATION = "IN_PREPARATION"
    SUBMITTED = "SUBMITTED"
    UNDER_REVIEW = "UNDER_REVIEW"
    ADDITIONAL_INFO_REQUESTED = "ADDITIONAL_INFO_REQUESTED"
    APPROVED = "APPROVED"
    REJECTED = "REJECTED"
    WITHDRAWN = "WITHDRAWN"

@dataclass
class RegulatorySubmission:
    submission_id: str
    product_name: str
    submission_type: SubmissionType
    submission_status: SubmissionStatus
    target_market: str
    submission_date: Optional[datetime.date] = None
    target_approval_date: Optional[datetime.date] = None
    actual_approval_date: Optional[datetime.date] = None
    regulatory_authority: str = ""
    responsible_person: str = ""
    notes: str = ""
    last_updated: datetime.date = datetime.date.today()

class RegulatoryTracker:
    def __init__(self, data_file: str = "regulatory_submissions.json"):
        self.data_file = data_file
        self.submissions: Dict[str, RegulatorySubmission] = {}
        self.load_data()
    
    def load_data(self):
        """Load existing submission data from JSON file"""
        try:
            with open(self.data_file, 'r') as f:
                data = json.load(f)
                for sub_id, sub_data in data.items():
                    # Convert date strings back to date objects
                    for date_field in ['submission_date', 'target_approval_date', 
                                     'actual_approval_date', 'last_updated']:
                        if sub_data.get(date_field):
                            sub_data[date_field] = datetime.datetime.strptime(
                                sub_data[date_field], '%Y-%m-%d').date()
                    
                    # Convert enums
                    sub_data['submission_type'] = SubmissionType(sub_data['submission_type'])
                    sub_data['submission_status'] = SubmissionStatus(sub_data['submission_status'])
                    
                    self.submissions[sub_id] = RegulatorySubmission(**sub_data)
        except FileNotFoundError:
            print(f"No existing data file found. Starting fresh.")
        except Exception as e:
            print(f"Error loading data: {e}")
    
    def save_data(self):
        """Save submission data to JSON file"""
        data = {}
        for sub_id, submission in self.submissions.items():
            sub_dict = asdict(submission)
            # Convert date objects to strings
            for date_field in ['submission_date', 'target_approval_date', 
                             'actual_approval_date', 'last_updated']:
                if sub_dict.get(date_field):
                    sub_dict[date_field] = sub_dict[date_field].strftime('%Y-%m-%d')
            
            # Convert enums to strings
            sub_dict['submission_type'] = sub_dict['submission_type'].value
            sub_dict['submission_status'] = sub_dict['submission_status'].value
            
            data[sub_id] = sub_dict
        
        with open(self.data_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def add_submission(self, submission: RegulatorySubmission):
        """Add new regulatory submission"""
        self.submissions[submission.submission_id] = submission
        self.save_data()
        print(f"Added submission: {submission.submission_id}")
    
    def update_submission_status(self, submission_id: str, 
                               new_status: SubmissionStatus, 
                               notes: str = ""):
        """Update submission status"""
        if submission_id in self.submissions:
            self.submissions[submission_id].submission_status = new_status
            self.submissions[submission_id].notes = notes
            self.submissions[submission_id].last_updated = datetime.date.today()
            self.save_data()
            print(f"Updated {submission_id} status to {new_status.value}")
        else:
            print(f"Submission {submission_id} not found")
    
    def get_submissions_by_status(self, status: SubmissionStatus) -> List[RegulatorySubmission]:
        """Get all submissions with specific status"""
        return [sub for sub in self.submissions.values() if sub.submission_status == status]
    
    def get_overdue_submissions(self) -> List[RegulatorySubmission]:
        """Get submissions that are overdue"""
        today = datetime.date.today()
        overdue = []
        for submission in self.submissions.values():
            if (submission.target_approval_date and 
                submission.target_approval_date < today and 
                submission.submission_status not in [SubmissionStatus.APPROVED, 
                                                   SubmissionStatus.REJECTED, 
                                                   SubmissionStatus.WITHDRAWN]):
                overdue.append(submission)
        return overdue
    
    def generate_status_report(self) -> str:
        """Generate comprehensive status report"""
        report = []
        report.append("REGULATORY SUBMISSION STATUS REPORT")
        report.append("=" * 50)
        report.append(f"Generated: {datetime.date.today()}")
        report.append("")
        
        # Summary by status
        status_counts = {}
        for status in SubmissionStatus:
            count = len(self.get_submissions_by_status(status))
            if count > 0:
                status_counts[status] = count
        
        report.append("SUBMISSION STATUS SUMMARY:")
        for status, count in status_counts.items():
            report.append(f"  {status.value}: {count}")
        report.append("")
        
        # Overdue submissions
        overdue = self.get_overdue_submissions()
        if overdue:
            report.append("OVERDUE SUBMISSIONS:")
            for submission in overdue:
                days_overdue = (datetime.date.today() - submission.target_approval_date).days
                report.append(f"  {submission.submission_id} - {days_overdue} days overdue")
            report.append("")
        
        # Active submissions requiring attention
        active_statuses = [SubmissionStatus.SUBMITTED, SubmissionStatus.UNDER_REVIEW, 
                          SubmissionStatus.ADDITIONAL_INFO_REQUESTED]
        active_submissions = []
        for status in active_statuses:
            active_submissions.extend(self.get_submissions_by_status(status))
        
        if active_submissions:
            report.append("ACTIVE SUBMISSIONS REQUIRING ATTENTION:")
            for submission in active_submissions:
                report.append(f"  {submission.submission_id} - {submission.product_name}")
                report.append(f"    Status: {submission.submission_status.value}")
                report.append(f"    Target Date: {submission.target_approval_date}")
                report.append(f"    Authority: {submission.regulatory_authority}")
                report.append("")
        
        return "\n".join(report)

def main():
    """Main function for command-line usage"""
    tracker = RegulatoryTracker()
    
    # Generate and print status report
    print(tracker.generate_status_report())
    
    # Example: Add a new submission
    # new_submission = RegulatorySubmission(
    #     submission_id="SUB-2024-001",
    #     product_name="HealthTech Device X",
    #     submission_type=SubmissionType.FDA_510K,
    #     submission_status=SubmissionStatus.PLANNING,
    #     target_market="United States",
    #     target_approval_date=datetime.date(2024, 12, 31),
    #     regulatory_authority="FDA",
    #     responsible_person="John Doe"
    # )
    # tracker.add_submission(new_submission)

if __name__ == "__main__":
    main()
