#!/usr/bin/env python3
"""
PIMP SMACK Data Collector
==========================
Extracts legal data from documents and builds MASTER_CASE_CONFIG over time.
Every skill imports this to read/write case data.

Features:
- Extracts case numbers, party names, citations
- Detects completed sections
- Awards pimp cards for milestones
- Persists everything to MASTER_CASE_CONFIG.json

Usage:
    from pimp_collector import PimpCollector
    
    collector = PimpCollector()
    collector.extract_from_docx("my_brief.docx")
    collector.save()
"""

import json
import re
from pathlib import Path
from datetime import datetime
from typing import Optional

try:
    from docx import Document
except ImportError:
    Document = None


class PimpCollector:
    """Collects and persists case data across all PIMP skills."""
    
    def __init__(self, config_path: Optional[str] = None):
        self.app_dir = Path(__file__).parent
        self.config_path = Path(config_path) if config_path else self.app_dir / "MASTER_CASE_CONFIG.json"
        
        # Load or initialize config
        self.config = self.load_config()
        
        # Extraction patterns
        self.patterns = {
            'ninth_circuit_no': r'(?:No\.|Case\s*(?:No\.?)?)\s*(\d{2}-\d{4,5})',
            'district_case_no': r'(?:Case\s*(?:No\.?)?|No\.)\s*(\d:\d{2}-cv-\d{5}(?:-[A-Z]+)?)',
            'case_citation': r'([A-Z][A-Za-z\'\-\s]+(?:v\.|vs\.)\s+[A-Z][A-Za-z\'\-\s,]+),?\s*(\d+\s+(?:U\.S\.|F\.\d+[d]?|F\.\s*(?:Supp\.|App\'x)|S\.\s*Ct\.)\s*\d+)',
            'usc_citation': r'(\d+)\s+U\.S\.C\.\s*§\s*(\d+[a-z]?(?:\([a-z0-9]+\))?)',
            'frap_citation': r'(Fed\.\s*R\.\s*App\.\s*P\.\s*\d+(?:\([a-z]\))?)',
            'frcp_citation': r'(Fed\.\s*R\.\s*Civ\.\s*P\.\s*\d+(?:\([a-z]\))?)',
            'judge_name': r'(?:Hon\.|Honorable|Judge)\s+([A-Z][a-z]+\s+[A-Z][a-z]+)',
        }
        
        # Known section headings to detect
        self.section_keywords = {
            'introduction': ['INTRODUCTION'],
            'jurisdictional_statement': ['JURISDICTIONAL STATEMENT', 'JURISDICTION'],
            'issues_presented': ['STATEMENT OF ISSUES', 'ISSUES PRESENTED', 'QUESTIONS PRESENTED'],
            'statement_of_case': ['STATEMENT OF THE CASE', 'STATEMENT OF CASE'],
            'statement_of_facts': ['STATEMENT OF FACTS', 'FACTUAL BACKGROUND'],
            'summary_of_argument': ['SUMMARY OF ARGUMENT', 'SUMMARY OF THE ARGUMENT'],
            'standard_of_review': ['STANDARD OF REVIEW'],
            'argument': ['ARGUMENT'],
            'conclusion': ['CONCLUSION'],
            'related_cases': ['RELATED CASES', 'STATEMENT OF RELATED CASES'],
            'certificate_compliance': ['CERTIFICATE OF COMPLIANCE'],
            'certificate_service': ['CERTIFICATE OF SERVICE'],
            'addendum': ['ADDENDUM'],
            'legal_standard': ['LEGAL STANDARD'],
            'procedural_history': ['PROCEDURAL HISTORY', 'PROCEDURAL BACKGROUND'],
        }
    
    def load_config(self) -> dict:
        """Load existing config or create new one."""
        if self.config_path.exists():
            with open(self.config_path, 'r', encoding='utf-8') as f:
                config = json.load(f)
            # Ensure all required keys exist (handle old config versions)
            default = self.get_default_config()
            for key in default:
                if key not in config:
                    config[key] = default[key]
            # Ensure nested keys exist
            if "citations_collected" not in config:
                config["citations_collected"] = {"cases": [], "statutes": [], "rules": []}
            if "completed_sections" not in config:
                config["completed_sections"] = {}
            if "pimp_cards_earned" not in config:
                config["pimp_cards_earned"] = []
            if "session_history" not in config:
                config["session_history"] = []
            return config
        return self.get_default_config()
    
    def get_default_config(self) -> dict:
        """Default empty config structure."""
        return {
            "_schema_version": "1.0.0",
            "_last_updated": "",
            "case_info": {
                "ninth_circuit_no": "",
                "district_case_no": "",
                "district_court": "",
                "judge": "",
            },
            "parties": {
                "appellant": {"name": "", "pro_se": True},
                "appellees": []
            },
            "citations_collected": {
                "cases": [],
                "statutes": [],
                "rules": []
            },
            "completed_sections": {},
            "pimp_cards_earned": [],
            "session_history": []
        }
    
    def save(self):
        """Save config to file."""
        self.config["_last_updated"] = datetime.now().isoformat()
        with open(self.config_path, 'w', encoding='utf-8') as f:
            json.dump(self.config, f, indent=2)
        print(f"[COLLECTOR] Saved config to {self.config_path}")
    
    def extract_from_text(self, text: str) -> dict:
        """Extract all legal data from text content."""
        extracted = {
            "case_numbers": [],
            "citations": {"cases": [], "statutes": [], "rules": []},
            "judges": [],
            "sections_found": []
        }
        
        # Extract case numbers
        ninth_matches = re.findall(self.patterns['ninth_circuit_no'], text)
        for match in ninth_matches:
            if match not in extracted["case_numbers"]:
                extracted["case_numbers"].append(match)
                if not self.config["case_info"]["ninth_circuit_no"]:
                    self.config["case_info"]["ninth_circuit_no"] = match
                    print(f"[COLLECTOR] Found 9th Circuit case: {match}")
        
        district_matches = re.findall(self.patterns['district_case_no'], text)
        for match in district_matches:
            if match not in extracted["case_numbers"]:
                extracted["case_numbers"].append(match)
                if not self.config["case_info"]["district_case_no"]:
                    self.config["case_info"]["district_case_no"] = match
                    print(f"[COLLECTOR] Found district case: {match}")
        
        # Extract case citations
        case_matches = re.findall(self.patterns['case_citation'], text)
        for match in case_matches:
            citation = f"{match[0].strip()}, {match[1]}"
            if citation not in self.config["citations_collected"]["cases"]:
                self.config["citations_collected"]["cases"].append(citation)
                extracted["citations"]["cases"].append(citation)
                print(f"[COLLECTOR] Found case: {citation[:50]}...")
        
        # Extract statute citations
        usc_matches = re.findall(self.patterns['usc_citation'], text)
        for match in usc_matches:
            citation = f"{match[0]} U.S.C. § {match[1]}"
            if citation not in self.config["citations_collected"]["statutes"]:
                self.config["citations_collected"]["statutes"].append(citation)
                extracted["citations"]["statutes"].append(citation)
        
        # Extract FRAP/FRCP citations
        frap_matches = re.findall(self.patterns['frap_citation'], text)
        frcp_matches = re.findall(self.patterns['frcp_citation'], text)
        for match in frap_matches + frcp_matches:
            if match not in self.config["citations_collected"]["rules"]:
                self.config["citations_collected"]["rules"].append(match)
                extracted["citations"]["rules"].append(match)
        
        # Extract judge names
        judge_matches = re.findall(self.patterns['judge_name'], text)
        for match in judge_matches:
            if match not in extracted["judges"]:
                extracted["judges"].append(match)
                if not self.config["case_info"]["judge"]:
                    self.config["case_info"]["judge"] = f"Hon. {match}"
                    print(f"[COLLECTOR] Found judge: {match}")
        
        # Detect sections
        text_upper = text.upper()
        for section_key, keywords in self.section_keywords.items():
            for keyword in keywords:
                if keyword in text_upper:
                    if section_key not in extracted["sections_found"]:
                        extracted["sections_found"].append(section_key)
                        self.config["completed_sections"][section_key] = True
                        print(f"[COLLECTOR] Found section: {section_key}")
                        self.pimp_smack(section_key)
                    break
        
        return extracted
    
    def extract_from_docx(self, docx_path: str) -> dict:
        """Extract data from a DOCX file."""
        if Document is None:
            print("[COLLECTOR] python-docx not installed, skipping DOCX extraction")
            return {}
        
        print(f"\n[COLLECTOR] Extracting from: {docx_path}")
        
        doc = Document(docx_path)
        full_text = "\n".join([para.text for para in doc.paragraphs])
        
        extracted = self.extract_from_text(full_text)
        
        # Log session
        self.log_session("extract_docx", docx_path, extracted)
        
        return extracted
    
    def extract_from_txt(self, txt_path: str) -> dict:
        """Extract data from a text file."""
        print(f"\n[COLLECTOR] Extracting from: {txt_path}")
        
        with open(txt_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        extracted = self.extract_from_text(content)
        
        # Log session
        self.log_session("extract_txt", txt_path, extracted)
        
        return extracted
    
    def log_session(self, action: str, file_path: str, data: dict):
        """Log what was done in this session."""
        session = {
            "timestamp": datetime.now().isoformat(),
            "action": action,
            "file": str(file_path),
            "items_found": {
                "case_numbers": len(data.get("case_numbers", [])),
                "citations": len(data.get("citations", {}).get("cases", [])),
                "sections": len(data.get("sections_found", []))
            }
        }
        self.config["session_history"].append(session)
        
        # Keep only last 50 sessions
        if len(self.config["session_history"]) > 50:
            self.config["session_history"] = self.config["session_history"][-50:]
    
    def pimp_smack(self, section_key: str):
        """Print a PIMP SMACK message when section is complete."""
        smacks = {
            "introduction": "PIMP SMACK! You introduced yourself like a boss.",
            "jurisdictional_statement": "PIMP SMACK! Jurisdiction locked down.",
            "issues_presented": "PIMP SMACK! Issues laid out clean.",
            "statement_of_case": "PIMP SMACK! Your story is on the record.",
            "statement_of_facts": "PIMP SMACK! Facts don't lie.",
            "summary_of_argument": "PIMP SMACK! Summary delivered with the white glove.",
            "standard_of_review": "PIMP SMACK! You know the rules.",
            "argument": "PIMP SMACK! Argument dropped. Corruption slapped.",
            "conclusion": "PIMP SMACK! Case closed.",
            "legal_standard": "PIMP SMACK! Legal standard cited.",
        }
        
        msg = smacks.get(section_key)
        if msg:
            print(f"\n  >>> {msg}")
        
        # Check if full brief is complete
        required = ["introduction", "jurisdictional_statement", "issues_presented",
                   "statement_of_case", "summary_of_argument", "standard_of_review",
                   "argument", "conclusion"]
        
        all_done = all(self.config["completed_sections"].get(s, False) for s in required)
        if all_done and not self.config.get("_brief_complete_shown"):
            self.config["_brief_complete_shown"] = True
            print(f"\n{'='*60}")
            print("  FULL PIMP SMACK! Brief is ready to file.")
            print("  Go slap some corruption with that white glove.")
            print(f"{'='*60}\n")
    
    def set_case_info(self, **kwargs):
        """Manually set case info."""
        for key, value in kwargs.items():
            if key in self.config["case_info"]:
                self.config["case_info"][key] = value
                print(f"[COLLECTOR] Set {key}: {value}")
    
    def set_appellant(self, name: str, pro_se: bool = True, **kwargs):
        """Set appellant info."""
        self.config["parties"]["appellant"]["name"] = name
        self.config["parties"]["appellant"]["pro_se"] = pro_se
        for key, value in kwargs.items():
            self.config["parties"]["appellant"][key] = value
        print(f"[COLLECTOR] Set appellant: {name}")
    
    def add_appellee(self, name: str, **kwargs):
        """Add an appellee."""
        appellee = {"name": name, **kwargs}
        if appellee not in self.config["parties"]["appellees"]:
            self.config["parties"]["appellees"].append(appellee)
            print(f"[COLLECTOR] Added appellee: {name}")
    
    def get_case_number(self) -> str:
        """Get the primary case number."""
        return (self.config["case_info"]["ninth_circuit_no"] or 
                self.config["case_info"]["district_case_no"] or 
                "UNKNOWN")
    
    def get_stats(self) -> dict:
        """Get collection statistics."""
        sections_complete = sum(1 for v in self.config["completed_sections"].values() if v)
        
        return {
            "case_number": self.get_case_number(),
            "sections_complete": sections_complete,
            "citations_collected": len(self.config["citations_collected"]["cases"]),
            "statutes_collected": len(self.config["citations_collected"]["statutes"]),
            "rules_collected": len(self.config["citations_collected"]["rules"]),
            "sessions": len(self.config["session_history"])
        }
    
    def print_status(self):
        """Print current collection status."""
        stats = self.get_stats()
        
        print("\n" + "=" * 60)
        print("PIMP SMACK CASE STATUS")
        print("=" * 60)
        print(f"Case Number: {stats['case_number']}")
        print(f"Sections Complete: {stats['sections_complete']}")
        print(f"Case Citations: {stats['citations_collected']}")
        print(f"Statutes: {stats['statutes_collected']}")
        print(f"Rules: {stats['rules_collected']}")
        print("=" * 60 + "\n")


def main():
    """CLI for testing collector."""
    import argparse
    
    parser = argparse.ArgumentParser(description='PIMP SMACK Data Collector')
    parser.add_argument('--extract', type=str, help='Extract from file (DOCX or TXT)')
    parser.add_argument('--status', action='store_true', help='Show current status')
    parser.add_argument('--set-case', type=str, help='Set 9th Circuit case number')
    parser.add_argument('--set-appellant', type=str, help='Set appellant name')
    
    args = parser.parse_args()
    
    collector = PimpCollector()
    
    if args.extract:
        path = Path(args.extract)
        if path.suffix.lower() == '.docx':
            collector.extract_from_docx(args.extract)
        else:
            collector.extract_from_txt(args.extract)
        collector.save()
    
    if args.set_case:
        collector.set_case_info(ninth_circuit_no=args.set_case)
        collector.save()
    
    if args.set_appellant:
        collector.set_appellant(args.set_appellant)
        collector.save()
    
    if args.status or not any([args.extract, args.set_case, args.set_appellant]):
        collector.print_status()


if __name__ == '__main__':
    main()
