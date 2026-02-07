#!/usr/bin/env python3
"""
Brief Validator & Compliance Checker
Validates all data files and checks FRAP compliance
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime


class ComplianceRules:
    """FRAP and Ninth Circuit compliance rules"""
    
    # Word limits (FRAP 32)
    WORD_LIMITS = {
        "opening_brief": 14000,
        "answering_brief": 14000,
        "reply_brief": 7000,
        "cross_appeal_brief": 16500,
    }
    
    # Required sections (FRAP 28)
    REQUIRED_SECTIONS = [
        "disclosure_statement",      # FRAP 26.1
        "table_of_contents",         # FRAP 28(a)(2)
        "table_of_authorities",      # FRAP 28(a)(3)
        "jurisdictional_statement",  # FRAP 28(a)(4)
        "issues_presented",          # FRAP 28(a)(5)
        "statement_of_case",         # FRAP 28(a)(6)
        "summary_of_argument",       # FRAP 28(a)(7)
        "argument",                  # FRAP 28(a)(8)
        "conclusion",                # FRAP 28(a)(9)
        "certificate_of_compliance", # FRAP 32(g)
        "certificate_of_service",    # FRAP 25(d)
    ]
    
    # Optional but recommended
    OPTIONAL_SECTIONS = [
        "introduction",              # Not required but helpful
        "standard_of_review",        # Can be in argument section
        "addendum",                  # For statutes/regulations
        "statement_of_related_cases" # 9th Cir. R. 28-2.6
    ]
    
    # Citation format patterns
    CITATION_PATTERNS = {
        "case": r"^.+,\s*\d+\s+(U\.S\.|F\.\d+[d]?|S\.\s*Ct\.)\s*\d+",
        "statute": r"^\d+\s+U\.S\.C\.\s*§\s*\d+",
        "rule_frap": r"^(Fed\.\s*R\.\s*App\.\s*P\.|FRAP)\s*\d+",
        "rule_frcp": r"^(Fed\.\s*R\.\s*Civ\.\s*P\.|FRCP)\s*\d+",
        "constitution": r"^U\.S\.\s*Const\.\s*amend\.\s*(I|II|III|IV|V|VI|VII|VIII|IX|X|XI|XII|XIII|XIV|XV)",
        "er_cite": r"^(\d+-)?ER-\d+",
    }
    
    # Formatting requirements
    FORMATTING = {
        "font_size_min": 14,  # points
        "margin_min": 1.0,    # inches
        "line_spacing": "double",
        "page_size": "letter",  # 8.5 x 11
    }


class BriefValidator:
    """Validate brief data and check compliance"""
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.info: List[str] = []
    
    def validate_all(self) -> Tuple[bool, Dict]:
        """Run all validations and return results"""
        
        self.errors = []
        self.warnings = []
        self.info = []
        
        print("\n" + "="*60)
        print("BRIEF VALIDATION & COMPLIANCE CHECK")
        print("="*60)
        
        # Load all data files
        data = self._load_all_data()
        
        if not data:
            return False, {"errors": self.errors, "warnings": self.warnings, "info": self.info}
        
        # Run validations
        self._validate_case_info(data.get('case_info', {}))
        self._validate_authorities(data.get('authorities', {}))
        self._validate_evidence_pool(data.get('evidence_pool', {}))
        self._validate_arguments(data.get('arguments', {}))
        self._validate_issues(data.get('issues_presented', {}))
        self._validate_timeline(data.get('timeline', {}))
        self._validate_cross_references(data)
        self._check_compliance(data)
        
        # Print results
        self._print_results()
        
        is_valid = len(self.errors) == 0
        
        return is_valid, {
            "errors": self.errors,
            "warnings": self.warnings,
            "info": self.info,
            "valid": is_valid
        }
    
    def _load_all_data(self) -> Optional[Dict]:
        """Load all JSON data files"""
        data = {}
        files = {
            'case_info': 'case_info.json',
            'authorities': 'authorities.json',
            'evidence_pool': 'evidence_pool.json',
            'arguments': 'arguments.json',
            'issues_presented': 'issues_presented.json',
            'timeline': 'timeline.json',
            'argument_content': 'argument_content.json',
        }
        
        for key, filename in files.items():
            path = self.data_dir / filename
            if path.exists():
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        data[key] = json.load(f)
                    self.info.append(f"✓ Loaded {filename}")
                except json.JSONDecodeError as e:
                    self.errors.append(f"JSON syntax error in {filename}: {e}")
            else:
                if key in ['case_info', 'authorities', 'arguments']:
                    self.errors.append(f"Missing required file: {filename}")
                else:
                    self.warnings.append(f"Optional file not found: {filename}")
        
        return data if not any("JSON syntax error" in e for e in self.errors) else None
    
    def _validate_case_info(self, case_info: Dict):
        """Validate case information"""
        print("\n--- Validating Case Info ---")
        
        # Required fields
        case = case_info.get('case', {})
        required = ['ninth_circuit_number', 'district_court_number', 'district_court']
        
        for field in required:
            if not case.get(field):
                self.errors.append(f"Missing case.{field} in case_info.json")
        
        # Validate case number format
        case_num = case.get('ninth_circuit_number', '')
        if case_num and not re.match(r'^\d{2}-\d+$', case_num):
            self.warnings.append(f"Case number format may be incorrect: {case_num} (expected XX-XXXX)")
        
        # Check parties
        parties = case_info.get('parties', {})
        if not parties.get('appellant', {}).get('name'):
            self.errors.append("Missing appellant name in case_info.json")
        if not parties.get('appellee', {}).get('name'):
            self.errors.append("Missing appellee name in case_info.json")
        
        # Check jurisdiction
        juris = case_info.get('jurisdiction', {})
        if not juris.get('district_court_basis'):
            self.warnings.append("Missing district court jurisdiction basis")
        if not juris.get('appeals_court_basis'):
            self.warnings.append("Missing appeals court jurisdiction basis")
    
    def _validate_authorities(self, authorities: Dict):
        """Validate citations and authorities"""
        print("\n--- Validating Authorities ---")
        
        cases = authorities.get('cases', [])
        statutes = authorities.get('statutes', [])
        rules = authorities.get('rules', [])
        
        # Check case citations
        for case in cases:
            bluebook = case.get('bluebook', '')
            if not bluebook:
                self.errors.append(f"Missing bluebook citation for case: {case.get('name', 'unknown')}")
            elif not re.search(r'\d+\s+(U\.S\.|F\.\d*d?|S\.\s*Ct\.)', bluebook):
                self.warnings.append(f"Check citation format: {bluebook}")
            
            if not case.get('pages_cited'):
                self.warnings.append(f"No pages cited for: {case.get('name', 'unknown')}")
        
        # Check for required citations (common in civil rights cases)
        case_names = [c.get('name', '').lower() for c in cases]
        
        if '1983' in str(statutes) or 'civil rights' in str(authorities).lower():
            if not any('monell' in name for name in case_names):
                self.warnings.append("Consider citing Monell for § 1983 municipal liability")
            if not any('iqbal' in name for name in case_names):
                self.warnings.append("Consider citing Ashcroft v. Iqbal for pleading standard")
        
        self.info.append(f"Found {len(cases)} cases, {len(statutes)} statutes, {len(rules)} rules")
    
    def _validate_evidence_pool(self, evidence_pool: Dict):
        """Validate evidence pool data"""
        print("\n--- Validating Evidence Pool ---")
        
        facts = evidence_pool.get('facts', [])
        evidence = evidence_pool.get('evidence', [])
        
        if not facts:
            self.warnings.append("Evidence pool has no facts - add facts to evidence_pool.json")
            return
        
        # Build evidence ID lookup
        evidence_ids = {e['id'] for e in evidence}
        fact_ids = {f['id'] for f in facts}
        
        for fact in facts:
            # Check required fields
            if not fact.get('statement'):
                self.errors.append(f"Fact {fact.get('id', '?')} missing statement")
            
            if not fact.get('record_cite'):
                self.warnings.append(f"Fact {fact.get('id', '?')} missing record citation")
            
            # Validate ER citation format
            cite = fact.get('record_cite', '')
            if cite and not re.match(r'^(\d+-)?ER-\d+|ECF\s*\d+', cite):
                self.warnings.append(f"Check citation format for {fact.get('id')}: {cite}")
            
            # Check cross-reference validity
            for ref in fact.get('cross_references', []):
                if ref not in fact_ids:
                    self.errors.append(f"Invalid cross-reference in {fact.get('id')}: {ref} does not exist")
            
            # Check evidence links
            for ev_id in fact.get('supporting_evidence', []):
                if ev_id not in evidence_ids:
                    self.errors.append(f"Invalid evidence reference in {fact.get('id')}: {ev_id} does not exist")
        
        self.info.append(f"Found {len(facts)} facts with {len(evidence)} evidence items")
    
    def _validate_arguments(self, arguments: Dict):
        """Validate argument structure"""
        print("\n--- Validating Arguments ---")
        
        args = arguments.get('arguments', [])
        
        if not args:
            self.errors.append("No arguments defined in arguments.json")
            return
        
        for arg in args:
            if not arg.get('heading'):
                self.errors.append(f"Argument {arg.get('number', '?')} missing heading")
            
            # Check heading is in proper format (caps for main arguments)
            heading = arg.get('heading', '')
            if heading and not heading.isupper():
                self.warnings.append(f"Main argument headings should be ALL CAPS: {arg.get('number')}")
            
            # Check subarguments
            for sub in arg.get('subarguments', []):
                if not sub.get('heading'):
                    self.errors.append(f"Subargument {arg.get('number')}.{sub.get('letter', '?')} missing heading")
        
        self.info.append(f"Found {len(args)} main arguments")
    
    def _validate_issues(self, issues: Dict):
        """Validate issues presented"""
        print("\n--- Validating Issues ---")
        
        issue_list = issues.get('issues', [])
        
        if not issue_list:
            self.errors.append("No issues defined in issues_presented.json")
            return
        
        for issue in issue_list:
            statement = issue.get('issue_statement', '')
            
            # Check it's a single sentence
            if statement.count('.') > 2:  # Allow for citations
                self.warnings.append(f"Issue {issue.get('number')} may be too long - should be one sentence")
            
            # Check for "Whether" format
            if not statement.lower().startswith('whether'):
                self.warnings.append(f"Issue {issue.get('number')} should start with 'Whether'")
            
            # Check for standard of review
            if not issue.get('standard_of_review'):
                self.warnings.append(f"Issue {issue.get('number')} missing standard of review")
        
        self.info.append(f"Found {len(issue_list)} issues")
    
    def _validate_timeline(self, timeline: Dict):
        """Validate timeline events"""
        print("\n--- Validating Timeline ---")
        
        events = timeline.get('events', [])
        
        if not events:
            self.warnings.append("No timeline events - add to timeline.json for Statement of Case")
            return
        
        # Check date format and ordering
        dates = []
        for event in events:
            date_str = event.get('date', '')
            if date_str:
                try:
                    # Handle date ranges
                    if ' to ' in date_str:
                        date_str = date_str.split(' to ')[0]
                    if not date_str.startswith('20') and not date_str.startswith('19'):
                        continue
                    date = datetime.strptime(date_str[:10], '%Y-%m-%d')
                    dates.append((date, event.get('event', '')))
                except ValueError:
                    self.warnings.append(f"Invalid date format: {date_str}")
            
            if not event.get('er_cite') and not event.get('ecf'):
                self.warnings.append(f"Event missing record cite: {event.get('event', '')[:50]}...")
        
        # Check chronological order
        if dates:
            sorted_dates = sorted(dates, key=lambda x: x[0])
            if dates != sorted_dates:
                self.warnings.append("Timeline events may not be in chronological order")
        
        self.info.append(f"Found {len(events)} timeline events")
    
    def _validate_cross_references(self, data: Dict):
        """Validate cross-references between files"""
        print("\n--- Validating Cross-References ---")
        
        # Get all authority citations
        authorities = data.get('authorities', {})
        case_names = {c.get('name', '').lower() for c in authorities.get('cases', [])}
        
        # Check arguments reference valid authorities
        arguments = data.get('arguments', {})
        for arg in arguments.get('arguments', []):
            for sub in arg.get('subarguments', []):
                for citation in sub.get('citations', []):
                    if citation.lower() not in case_names:
                        # Could be a short form
                        if not any(citation.lower() in name for name in case_names):
                            self.warnings.append(f"Citation '{citation}' in argument not found in authorities")
    
    def _check_compliance(self, data: Dict):
        """Check FRAP compliance"""
        print("\n--- Checking FRAP Compliance ---")
        
        # Check for required sections
        has_sections = {
            'disclosure_statement': True,  # Generated
            'table_of_contents': True,      # Generated
            'table_of_authorities': bool(data.get('authorities', {}).get('cases')),
            'jurisdictional_statement': bool(data.get('case_info', {}).get('jurisdiction')),
            'issues_presented': bool(data.get('issues_presented', {}).get('issues')),
            'statement_of_case': bool(data.get('timeline', {}).get('events')),
            'summary_of_argument': True,  # Placeholder in template
            'argument': bool(data.get('arguments', {}).get('arguments')),
            'conclusion': True,  # Generated
            'certificate_of_compliance': True,  # Generated
            'certificate_of_service': True,  # Generated
        }
        
        for section, present in has_sections.items():
            if not present:
                self.errors.append(f"Missing required section: {section}")
        
        # 9th Circuit specific
        self.info.append("Checking 9th Circuit specific requirements...")
        
        # Record citations format
        evidence_pool = data.get('evidence_pool', {})
        for fact in evidence_pool.get('facts', []):
            cite = fact.get('record_cite', '')
            if cite and not re.match(r'^(\d+-)?ER-\d+|ECF\s*\d+', cite):
                self.warnings.append(f"9th Cir: Citation should be in ER-XX format: {cite}")
    
    def _print_results(self):
        """Print validation results"""
        print("\n" + "="*60)
        print("VALIDATION RESULTS")
        print("="*60)
        
        if self.errors:
            print(f"\n❌ ERRORS ({len(self.errors)}):")
            for error in self.errors:
                print(f"   • {error}")
        
        if self.warnings:
            print(f"\n⚠️  WARNINGS ({len(self.warnings)}):")
            for warning in self.warnings:
                print(f"   • {warning}")
        
        if self.info:
            print(f"\nℹ️  INFO ({len(self.info)}):")
            for info in self.info:
                print(f"   • {info}")
        
        print("\n" + "-"*60)
        if not self.errors:
            print("✅ VALIDATION PASSED - Ready to generate brief")
        else:
            print("❌ VALIDATION FAILED - Fix errors before generating")
        print("-"*60 + "\n")


def main():
    """Run validation"""
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"
    
    validator = BriefValidator(str(data_dir))
    is_valid, results = validator.validate_all()
    
    return 0 if is_valid else 1


if __name__ == "__main__":
    exit(main())
