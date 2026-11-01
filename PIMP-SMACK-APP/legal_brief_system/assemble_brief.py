#!/usr/bin/env python3
"""
Brief Section Assembler
Copies EXACT text from JSON source files into brief template using markers.

*** CRITICAL: NO TEXT GENERATION ***
This script ONLY copies text from source files.
It does NOT generate, reword, or modify any content.

USAGE:
  python assemble_brief.py --section statement_of_case
  python assemble_brief.py --section all
  python assemble_brief.py --list-facts
"""

import json
import argparse
import shutil
import os
from pathlib import Path
from datetime import datetime


class SourceLoader:
    """
    Load exact text from source JSON files.
    READ-ONLY - never modifies source files.
    """
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
        self._cache = {}
    
    def _load_json(self, filename: str) -> dict:
        """Load JSON file - cached for efficiency"""
        if filename not in self._cache:
            path = self.data_dir / filename
            if path.exists():
                with open(path, 'r', encoding='utf-8') as f:
                    self._cache[filename] = json.load(f)
            else:
                print(f"WARNING: Source file not found: {path}")
                self._cache[filename] = {}
        return self._cache[filename]
    
    def get_case_info(self) -> dict:
        return self._load_json('case_info.json')
    
    def get_evidence_pool(self) -> dict:
        return self._load_json('evidence_pool.json')
    
    def get_authorities(self) -> dict:
        return self._load_json('authorities.json')
    
    def get_arguments(self) -> dict:
        return self._load_json('arguments.json')
    
    def get_issues(self) -> dict:
        return self._load_json('issues_presented.json')
    
    def get_timeline(self) -> dict:
        return self._load_json('timeline.json')
    
    def get_fact_by_id(self, fact_id: str) -> dict:
        """Get exact fact by ID - NO MODIFICATION"""
        pool = self.get_evidence_pool()
        for fact in pool.get('facts', []):
            if fact.get('id') == fact_id:
                return fact
        return None
    
    def get_facts_for_section(self, section_name: str) -> list:
        """Get all facts assigned to a section - EXACT as stored"""
        pool = self.get_evidence_pool()
        facts = []
        for fact in pool.get('facts', []):
            if section_name in fact.get('used_in_sections', []):
                facts.append(fact)
        # Sort by date if available
        return sorted(facts, key=lambda x: x.get('date', ''))
    
    def list_all_facts(self) -> list:
        """List all fact IDs and their statements - for reference"""
        pool = self.get_evidence_pool()
        return [(f['id'], f.get('statement', '')[:80]) for f in pool.get('facts', [])]


class SectionAssembler:
    """
    Assemble brief sections by copying exact text from sources.
    DOES NOT generate any content - only copies.
    """
    
    def __init__(self, data_dir: str):
        self.loader = SourceLoader(data_dir)
    
    def assemble_statement_of_case(self, fact_ids: list = None) -> str:
        """
        Assemble Statement of Case from exact facts.
        
        Args:
            fact_ids: List of fact IDs to include (in order).
                      If None, uses all facts tagged for 'statement_of_case'.
        
        Returns:
            Assembled text with facts and citations - EXACT from source.
        """
        if fact_ids:
            facts = [self.loader.get_fact_by_id(fid) for fid in fact_ids]
            facts = [f for f in facts if f is not None]
        else:
            facts = self.loader.get_facts_for_section('statement_of_case')
        
        paragraphs = []
        for fact in facts:
            # Get EXACT statement - no modification
            statement = fact.get('statement', '')
            cite = fact.get('record_cite', '')
            
            if cite:
                # Combine statement with citation
                text = f"{statement} ({cite}.)"
            else:
                text = statement
            
            paragraphs.append(text)
        
        return '\n\n'.join(paragraphs)
    
    def assemble_issues_presented(self) -> str:
        """Assemble Issues Presented - EXACT from source"""
        issues = self.loader.get_issues()
        
        lines = []
        for i, issue in enumerate(issues.get('issues', []), 1):
            # Get EXACT issue text
            text = issue.get('text', '')
            lines.append(f"{i}. {text}")
        
        return '\n\n'.join(lines)
    
    def assemble_jurisdictional_statement(self) -> str:
        """Assemble Jurisdictional Statement - EXACT from source"""
        case_info = self.loader.get_case_info()
        jurisdiction = case_info.get('jurisdiction', {})
        
        # Build from exact source fields
        parts = []
        
        if jurisdiction.get('district_court_basis'):
            parts.append(jurisdiction['district_court_basis'])
        
        if jurisdiction.get('appellate_basis'):
            parts.append(jurisdiction['appellate_basis'])
        
        if jurisdiction.get('judgment_date'):
            parts.append(f"The district court entered judgment on {jurisdiction['judgment_date']}.")
        
        if jurisdiction.get('notice_of_appeal_date'):
            parts.append(f"Appellant filed a timely notice of appeal on {jurisdiction['notice_of_appeal_date']}.")
        
        if jurisdiction.get('timeliness_rule'):
            parts.append(jurisdiction['timeliness_rule'])
        
        return ' '.join(parts)
    
    def assemble_argument(self, argument_id: str) -> str:
        """
        Assemble an Argument section.
        
        Args:
            argument_id: e.g., 'argument_I', 'argument_II'
        
        Returns:
            Argument text with supporting facts - EXACT from source.
        """
        arguments = self.loader.get_arguments()
        
        # Find the argument
        arg_data = None
        for arg in arguments.get('arguments', []):
            if arg.get('id') == argument_id:
                arg_data = arg
                break
        
        if not arg_data:
            return f"[ARGUMENT NOT FOUND: {argument_id}]"
        
        parts = []
        
        # Heading - EXACT
        if arg_data.get('heading'):
            parts.append(arg_data['heading'])
        
        # Standard of review if included
        if arg_data.get('standard_of_review'):
            parts.append(f"\nStandard of Review: {arg_data['standard_of_review']}")
        
        # Body text - EXACT
        if arg_data.get('body'):
            parts.append(f"\n{arg_data['body']}")
        
        # Supporting facts - EXACT with citations
        fact_ids = arg_data.get('supporting_facts', [])
        for fid in fact_ids:
            fact = self.loader.get_fact_by_id(fid)
            if fact:
                statement = fact.get('statement', '')
                cite = fact.get('record_cite', '')
                if cite:
                    parts.append(f"\n{statement} ({cite}.)")
                else:
                    parts.append(f"\n{statement}")
        
        return '\n'.join(parts)
    
    def assemble_conclusion(self) -> str:
        """Assemble Conclusion - EXACT from source"""
        case_info = self.loader.get_case_info()
        return case_info.get('conclusion', {}).get('text', 
            "For the foregoing reasons, the judgment of the district court should be reversed.")
    
    def assemble_disclosure(self) -> str:
        """Assemble Disclosure Statement - EXACT from source"""
        case_info = self.loader.get_case_info()
        parties = case_info.get('parties', {})
        appellant = parties.get('appellant', {})
        
        if appellant.get('pro_se'):
            return "Appellant is a natural person proceeding pro se and is not required to file a disclosure statement pursuant to FRAP 26.1."
        
        return case_info.get('disclosure_statement', {}).get('text', '')


def save_with_dual_copy(content: str, case_num: str, section_name: str, outbox_dir: Path):
    """
    Save section to OUTBOX with dual naming convention.
    """
    import stat
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    clean_case = case_num.replace(" ", "").replace("/", "-")
    clean_section = section_name.replace(" ", "_")
    
    # Section-specific directory
    section_dir = outbox_dir / "sections" / clean_section
    section_dir.mkdir(parents=True, exist_ok=True)
    
    # Chronological directory
    chrono_dir = outbox_dir / "chronological"
    chrono_dir.mkdir(parents=True, exist_ok=True)
    
    # Primary: {case}-{section}-{datetime}.txt
    primary_name = f"{clean_case}-{clean_section}-{timestamp}.txt"
    primary_path = section_dir / primary_name
    
    # Chronological: {datetime}-{case}-{section}.txt (read-only)
    chrono_name = f"{timestamp}-{clean_case}-{clean_section}.txt"
    chrono_path = chrono_dir / chrono_name
    
    # Write primary
    with open(primary_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    # Write chronological (read-only)
    with open(chrono_path, 'w', encoding='utf-8') as f:
        f.write(content)
    os.chmod(chrono_path, stat.S_IREAD)
    
    print(f"✓ Saved: {primary_path}")
    print(f"✓ Saved: {chrono_path} (read-only)")
    
    return primary_path, chrono_path


def main():
    parser = argparse.ArgumentParser(
        description='Assemble brief sections from source files (NO TEXT GENERATION)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
CRITICAL: This script ONLY copies exact text from your JSON source files.
It does NOT generate, reword, or modify any content.

Examples:
  python assemble_brief.py --section statement_of_case
  python assemble_brief.py --section argument_I
  python assemble_brief.py --list-facts
  python assemble_brief.py --section statement_of_case --facts F001,F002,F003
        """
    )
    parser.add_argument('--section', type=str, 
                        choices=['disclosure', 'jurisdictional', 'issues', 
                                'statement_of_case', 'argument_I', 'argument_II', 
                                'argument_III', 'conclusion', 'all'],
                        help='Section to assemble')
    parser.add_argument('--facts', type=str,
                        help='Comma-separated fact IDs to include (for statement_of_case)')
    parser.add_argument('--list-facts', action='store_true',
                        help='List all available facts')
    parser.add_argument('--validate', action='store_true',
                        help='Validate sources exist (no output)')
    
    args = parser.parse_args()
    
    # Setup paths
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"
    outbox_dir = script_dir.parent / "OUTBOX"
    outbox_dir.mkdir(exist_ok=True)
    
    assembler = SectionAssembler(str(data_dir))
    
    # List facts
    if args.list_facts:
        print("\n=== AVAILABLE FACTS ===")
        for fid, statement in assembler.loader.list_all_facts():
            print(f"  {fid}: {statement}...")
        return
    
    # Validate
    if args.validate:
        print("\n=== VALIDATING SOURCES ===")
        loader = assembler.loader
        print(f"  case_info.json: {'✓' if loader.get_case_info() else '✗'}")
        print(f"  evidence_pool.json: {'✓' if loader.get_evidence_pool() else '✗'}")
        print(f"  arguments.json: {'✓' if loader.get_arguments() else '✗'}")
        print(f"  issues_presented.json: {'✓' if loader.get_issues() else '✗'}")
        return
    
    if not args.section:
        parser.print_help()
        return
    
    # Get case number for naming
    case_info = assembler.loader.get_case_info()
    case_num = case_info.get('case', {}).get('ninth_circuit_number', 'XX-XXXX')
    
    # Assemble requested section
    print(f"\n=== ASSEMBLING: {args.section} ===")
    print("(Copying exact text from source files - NO generation)\n")
    
    if args.section == 'statement_of_case':
        fact_ids = args.facts.split(',') if args.facts else None
        content = assembler.assemble_statement_of_case(fact_ids)
    elif args.section == 'issues':
        content = assembler.assemble_issues_presented()
    elif args.section == 'jurisdictional':
        content = assembler.assemble_jurisdictional_statement()
    elif args.section == 'disclosure':
        content = assembler.assemble_disclosure()
    elif args.section == 'conclusion':
        content = assembler.assemble_conclusion()
    elif args.section.startswith('argument_'):
        content = assembler.assemble_argument(args.section)
    else:
        print(f"Section '{args.section}' not yet implemented")
        return
    
    # Display content
    print("--- ASSEMBLED CONTENT (exact from source) ---")
    print(content)
    print("--- END ---\n")
    
    # Save
    save_with_dual_copy(content, case_num, args.section, outbox_dir)


if __name__ == "__main__":
    main()
