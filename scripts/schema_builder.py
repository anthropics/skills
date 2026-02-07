#!/usr/bin/env python3
"""
Master Schema Builder - Extracts information from existing files and populates .MASTER_SCHEMA.json

This script learns from your documents over time:
- Scans OUTBOX directories for generated documents
- Extracts case information, party names, judges, etc.
- Populates the master schema so models don't have to ask repeatedly
- Identifies patterns in citations, facts, arguments
- TRACKS CHANGES since last run and logs them to .MASTER_LOG.csv
- MOVES processed documents to skill _examples folders with timestamps

The more documents you generate, the smarter the schema becomes.
"""

import json
import os
import re
import csv
import shutil
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
import zipfile
import xml.etree.ElementTree as ET

# Base directory
BASE_DIR = Path(__file__).parent.parent
MASTER_SCHEMA_PATH = BASE_DIR / ".MASTER_SCHEMA.json"
OUTBOX_DIR = BASE_DIR.parent / "OUTBOX"
MASTER_LOG_PATH = BASE_DIR / ".MASTER_LOG.csv"

# Map OUTBOX subdirectories to skills for moving files to _examples
OUTBOX_TO_SKILL = {
    'covers': 'ninth-circuit-cover',
    'declarations': 'declaration-builder',
    'briefs': 'ninth-circuit-opening-brief',
    'motions': 'universal-motion-brief',
    'sections': 'ninth-circuit-brief-body'
}


def load_master_schema() -> Dict[str, Any]:
    """Load existing master schema or return empty template"""
    if MASTER_SCHEMA_PATH.exists():
        with open(MASTER_SCHEMA_PATH, 'r', encoding='utf-8') as f:
            return json.load(f)
    return {}


def save_master_schema(schema: Dict[str, Any]) -> None:
    """Save updated master schema"""
    schema['last_updated'] = datetime.now().isoformat()
    with open(MASTER_SCHEMA_PATH, 'w', encoding='utf-8') as f:
        json.dump(schema, f, indent=2, ensure_ascii=False)
    print(f"✓ Updated {MASTER_SCHEMA_PATH}")


def log_change(change_type: str, details: str) -> None:
    """Log changes to .MASTER_LOG.csv
    
    Columns: TIMESTAMP | CHECK OR RUN | STATUS | CHANGES SINCE LAST RUN | 
             SKILL WORKED ON | MODEL RUNNING | MODEL READ INSTRUCTIONS/CLEAN FILES | 
             CHECK IN OR OUT | NOTE
    """
    timestamp = datetime.now().isoformat()
    
    # Create log file with headers if it doesn't exist
    if not MASTER_LOG_PATH.exists():
        with open(MASTER_LOG_PATH, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                'TIMESTAMP',
                'CHECK OR RUN', 
                'STATUS',
                'CHANGES SINCE LAST RUN',
                'SKILL WORKED ON',
                'MODEL RUNNING',
                'MODEL READ INSTRUCTIONS/CLEAN FILES',
                'CHECK IN OR OUT',
                'NOTE'
            ])
    
    # Append change
    with open(MASTER_LOG_PATH, 'a', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow([
            timestamp,
            'RUN',  # This is a RUN operation
            'SUCCESS',  # Assume success unless exception
            details,  # What changed
            'schema_builder',  # Skill/script
            'schema_builder.py',  # Model/script running
            'N/A',  # Not applicable for schema builder
            'UPDATE',  # This is an update operation
            change_type  # Type of change
        ])


def calculate_diff(old_schema: Dict[str, Any], new_schema: Dict[str, Any]) -> List[str]:
    """Calculate what changed between old and new schema
    
    Returns list of human-readable changes
    """
    changes = []
    
    # Check for new cases
    old_cases = set(old_schema.get('active_cases', {}).keys())
    new_cases = set(new_schema.get('active_cases', {}).keys())
    
    added_cases = new_cases - old_cases
    removed_cases = old_cases - new_cases
    
    # Filter out metadata keys
    added_cases = {c for c in added_cases if not c.startswith('_') and not c.startswith('example_')}
    removed_cases = {c for c in removed_cases if not c.startswith('_') and not c.startswith('example_')}
    
    for case in added_cases:
        changes.append(f"NEW CASE: {case}")
    
    for case in removed_cases:
        changes.append(f"REMOVED CASE: {case}")
    
    # Check for updated case information in existing cases
    for case_num in old_cases & new_cases:
        if case_num.startswith('_') or case_num.startswith('example_'):
            continue
        
        old_case = old_schema.get('active_cases', {}).get(case_num, {})
        new_case = new_schema.get('active_cases', {}).get(case_num, {})
        
        # Check judge
        old_judge = old_case.get('judge', {}).get('name', '')
        new_judge = new_case.get('judge', {}).get('name', '')
        if old_judge != new_judge and new_judge:
            changes.append(f"CASE {case_num}: Judge updated to '{new_judge}'")
        
        # Check filing history
        old_files = len(old_case.get('filing_history', []))
        new_files = len(new_case.get('filing_history', []))
        if new_files > old_files:
            changes.append(f"CASE {case_num}: +{new_files - old_files} new files")
    
    # Check for new citations
    old_citations = set(old_schema.get('learned_patterns', {}).get('common_citations', []))
    new_citations = set(new_schema.get('learned_patterns', {}).get('common_citations', []))
    
    added_citations = new_citations - old_citations
    if added_citations:
        changes.append(f"NEW CITATIONS: {len(added_citations)} learned")
    
    return changes


def extract_text_from_docx(docx_path: Path) -> str:
    """Extract text from DOCX file"""
    try:
        with zipfile.ZipFile(docx_path, 'r') as docx:
            xml_content = docx.read('word/document.xml')
            tree = ET.fromstring(xml_content)
            # Extract all text nodes
            namespace = {'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main'}
            paragraphs = tree.findall('.//w:t', namespace)
            return ' '.join([p.text for p in paragraphs if p.text])
    except Exception as e:
        print(f"Warning: Could not extract text from {docx_path}: {e}")
        return ""


def extract_case_number(text: str) -> Optional[str]:
    """Extract case number from text
    
    Real case numbers: YY-XXXXX (e.g., 25-6461)
    False positives to avoid: MM-YYYY dates (e.g., 28-2022)
    
    Rules:
    - First two digits must be 20-29 (year 2020-2029)
    - Second part must be 4-5 digits
    - Second part must NOT be a valid year (reject 2020-2029)
    """
    # Pattern: XX-XXXXX where XX is 20-29 and XXXXX is NOT 2020-2029
    pattern = r'\b(2[0-9])-(\d{4,5})\b'
    
    for match in re.finditer(pattern, text):
        year_part = match.group(1)
        number_part = match.group(2)
        
        # Reject if second part is a year (2020-2029)
        if len(number_part) == 4 and number_part.startswith('202'):
            continue  # This is a date like 28-2022, not a case number
        
        return f"{year_part}-{number_part}"
    
    return None


def extract_judge_name(text: str) -> Optional[str]:
    """Extract judge name from text"""
    # Pattern: Hon. [Name] or Judge [Name]
    patterns = [
        r'(?:Hon\.|Honorable|Judge)\s+([A-Z][a-z]+(?:\s+[A-Z][a-z]+)+)',
        r'Presiding:\s+([A-Z][a-z]+(?:\s+[A-Z][a-z]+)+)'
    ]
    for pattern in patterns:
        match = re.search(pattern, text)
        if match:
            return match.group(1)
    return None


def extract_parties(text: str) -> Dict[str, List[str]]:
    """Extract party names from text"""
    parties = {'appellants': [], 'appellees': []}
    
    # Pattern: [NAME], Appellant vs. [NAME], Appellee
    # This is a simplified version - would need more sophisticated NLP for real use
    appellant_pattern = r'([A-Z][A-Z\s\.]+),\s*(?:Appellant|Petitioner)'
    appellee_pattern = r'([A-Z][A-Z\s\.]+),\s*(?:Appellee|Respondent)'
    
    appellants = re.findall(appellant_pattern, text)
    appellees = re.findall(appellee_pattern, text)
    
    parties['appellants'] = [name.strip() for name in appellants]
    parties['appellees'] = [name.strip() for name in appellees]
    
    return parties


def extract_citations(text: str) -> List[str]:
    """Extract legal citations from text"""
    # Simplified citation patterns
    patterns = [
        r'\d+\s+U\.S\.C\.\s+§\s*\d+',  # USC citations
        r'\d+\s+F\.\d+d?\s+\d+',  # Federal reporter citations
        r'Fed\.\s*R\.\s*(?:Civ\.|App)\.\s*P\.\s*\d+',  # FRCP/FRAP citations
    ]
    
    citations = []
    for pattern in patterns:
        matches = re.findall(pattern, text)
        citations.extend(matches)
    
    return list(set(citations))  # Remove duplicates


def scan_outbox_directory_tracked(schema: Dict[str, Any]) -> Tuple[Dict[str, Any], List[Tuple[str, str]]]:
    """
    Scan OUTBOX directory for generated documents and extract information.
    Returns schema and list of (outbox_subdir, filename) tuples for file tracking.
    """
    
    processed_files = []
    
    if not OUTBOX_DIR.exists():
        print(f"Warning: OUTBOX directory not found at {OUTBOX_DIR}")
        return schema, processed_files
    
    print(f"\n=== Scanning {OUTBOX_DIR} ===")
    
    # Scan for DOCX files
    docx_files = list(OUTBOX_DIR.rglob("*.docx"))
    print(f"Found {len(docx_files)} DOCX files")
    
    all_citations = []
    cases_found = {}
    
    for docx_file in docx_files:
        print(f"Processing: {docx_file.name}")
        
        # Track which OUTBOX subdir this came from
        try:
            outbox_subdir = docx_file.relative_to(OUTBOX_DIR).parts[0]
            processed_files.append((outbox_subdir, docx_file.name))
        except (ValueError, IndexError):
            print(f"  ⚠ Could not determine OUTBOX subdirectory for {docx_file.name}")
        
        # Extract text
        text = extract_text_from_docx(docx_file)
        if not text:
            continue
        
        # Extract case number
        case_number = extract_case_number(text)
        if case_number:
            print(f"  ✓ Found case number: {case_number}")
            
            if case_number not in cases_found:
                cases_found[case_number] = {
                    'case_number': case_number,
                    'files': [],
                    'judge': None,
                    'parties': {'appellants': [], 'appellees': []}
                }
            
            cases_found[case_number]['files'].append({
                'filename': docx_file.name,
                'path': str(docx_file.relative_to(OUTBOX_DIR)),
                'date_processed': datetime.now().isoformat()
            })
            
            # Extract judge
            judge = extract_judge_name(text)
            if judge and not cases_found[case_number]['judge']:
                cases_found[case_number]['judge'] = judge
                print(f"  ✓ Found judge: {judge}")
            
            # Extract parties
            parties = extract_parties(text)
            if parties['appellants']:
                cases_found[case_number]['parties']['appellants'].extend(parties['appellants'])
                print(f"  ✓ Found appellants: {', '.join(parties['appellants'])}")
            if parties['appellees']:
                cases_found[case_number]['parties']['appellees'].extend(parties['appellees'])
                print(f"  ✓ Found appellees: {', '.join(parties['appellees'])}")
        
        # Extract citations
        citations = extract_citations(text)
        all_citations.extend(citations)
    
    # Update schema with found cases
    if 'active_cases' not in schema:
        schema['active_cases'] = {}
    
    for case_num, case_data in cases_found.items():
        # Deduplicate parties
        case_data['parties']['appellants'] = list(set(case_data['parties']['appellants']))
        case_data['parties']['appellees'] = list(set(case_data['parties']['appellees']))
        
        # Merge with existing case data
        if case_num in schema['active_cases']:
            existing = schema['active_cases'][case_num]
            # Update judge if new one found
            if case_data['judge']:
                existing['judge'] = case_data['judge']
            # Merge files
            existing.setdefault('filing_history', []).extend(case_data['files'])
            # Merge parties
            existing.setdefault('parties', {'appellants': [], 'appellees': []})
            existing['parties']['appellants'] = list(set(existing['parties']['appellants'] + case_data['parties']['appellants']))
            existing['parties']['appellees'] = list(set(existing['parties']['appellees'] + case_data['parties']['appellees']))
        else:
            schema['active_cases'][case_num] = {
                'case_number': case_num,
                'judge': case_data['judge'],
                'parties': case_data['parties'],
                'filing_history': case_data['files']
            }
    
    # Update learned citations
    if all_citations:
        schema.setdefault('learned_patterns', {})
        existing_citations = schema['learned_patterns'].get('common_citations', [])
        schema['learned_patterns']['common_citations'] = list(set(existing_citations + all_citations))
    
    print(f"\n✓ Extracted data from {len(docx_files)} files")
    print(f"✓ Found {len(cases_found)} cases")
    print(f"✓ Learned {len(all_citations)} unique citations")
    
    return schema, processed_files


def scan_outbox_directory(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Legacy wrapper for backward compatibility"""
    schema, _ = scan_outbox_directory_tracked(schema)
    return schema


def scan_json_configs(schema: Dict[str, Any]) -> Dict[str, Any]:
    """Scan existing JSON config files and merge relevant information"""
    
    print(f"\n=== Scanning for JSON configs ===")
    
    # Look for filing_config files
    config_patterns = [
        'filing_config.json',
        'filing_config_MASTER.json',
        'legal_styles_strict.json'
    ]
    
    for pattern in config_patterns:
        config_files = list(BASE_DIR.parent.rglob(pattern))
        for config_file in config_files:
            print(f"Found: {config_file.relative_to(BASE_DIR.parent)}")
            try:
                with open(config_file, 'r', encoding='utf-8') as f:
                    config_data = json.load(f)
                
                # Extract case information if present
                if 'case_number' in config_data:
                    case_num = config_data['case_number']
                    print(f"  ✓ Case number: {case_num}")
                    
                    if 'active_cases' not in schema:
                        schema['active_cases'] = {}
                    
                    if case_num not in schema['active_cases']:
                        schema['active_cases'][case_num] = {
                            'case_number': case_num,
                            'case_name': config_data.get('case_name', ''),
                            'jurisdiction': config_data.get('jurisdiction', 'ninth_circuit'),
                            'court_full_name': config_data.get('court_name', ''),
                            'judge': {'name': config_data.get('judge', ''), 'title': 'District Judge'},
                            'parties': config_data.get('parties', {'appellants': [], 'appellees': []}),
                            'filing_history': [],
                            'key_dates': config_data.get('key_dates', {})
                        }
                
            except Exception as e:
                print(f"  Warning: Could not parse {config_file}: {e}")
    
    return schema


def move_to_examples(processed_files: List[Tuple[str, str]]) -> List[str]:
    """
    Move processed OUTBOX files to skill _examples folders with timestamps.
    
    Args:
        processed_files: List of (outbox_subdir, filename) tuples
    
    Returns:
        List of status messages about what was moved
    """
    messages = []
    timestamp = datetime.now().strftime("%Y-%m-%d")
    
    for outbox_subdir, filename in processed_files:
        # Determine which skill this file belongs to
        skill_name = OUTBOX_TO_SKILL.get(outbox_subdir)
        if not skill_name:
            messages.append(f"⚠ Unknown OUTBOX subdir '{outbox_subdir}' for {filename}")
            continue
        
        skill_examples_dir = BASE_DIR / skill_name / "_examples"
        skill_examples_dir.mkdir(parents=True, exist_ok=True)
        
        # Build source and destination paths
        source_path = OUTBOX_DIR / outbox_subdir / filename
        
        # Add timestamp to filename: [YYYY-MM-DD]-original.docx
        timestamped_filename = f"[{timestamp}]-{filename}"
        dest_path = skill_examples_dir / timestamped_filename
        
        # Move file
        try:
            if source_path.exists():
                shutil.move(str(source_path), str(dest_path))
                messages.append(f"✓ Moved {filename} → {skill_name}/_examples/{timestamped_filename}")
            else:
                messages.append(f"⚠ File not found: {source_path}")
        except Exception as e:
            messages.append(f"✗ Error moving {filename}: {e}")
    
    return messages


def main():
    """Main execution"""
    print("=== Master Schema Builder ===")
    print("This tool learns from your documents and populates .MASTER_SCHEMA.json")
    print("so models can generate properly formatted documents without guessing.\n")
    
    # Load existing schema BEFORE any changes
    old_schema = load_master_schema()
    print(f"Loaded schema from {MASTER_SCHEMA_PATH}")
    
    # Make a copy for modification
    schema = old_schema.copy() if old_schema else {}
    
    # Track files we process for later moving
    processed_files = []
    
    # Scan OUTBOX directory
    schema, files_found = scan_outbox_directory_tracked(schema)
    processed_files.extend(files_found)
    
    # Scan JSON configs
    schema = scan_json_configs(schema)
    
    # Calculate what changed
    changes = calculate_diff(old_schema, schema)
    
    # Log changes
    if changes:
        print("\n=== Changes Since Last Run ===")
        for change in changes:
            print(f"  • {change}")
            log_change("SCHEMA_UPDATE", change)
    else:
        print("\n=== No Changes Detected ===")
        log_change("SCHEMA_CHECK", "No changes detected")
    
    # Save updated schema
    save_master_schema(schema)
    
    # Move processed files to _examples folders
    if processed_files:
        print("\n=== Moving Processed Files to _examples ===")
        move_messages = move_to_examples(processed_files)
        for msg in move_messages:
            print(f"  {msg}")
            log_change("FILE_MOVE", msg)
    
    print("\n=== Complete ===")
    print("The master schema has been updated with discovered information.")
    print("Models can now read .MASTER_SCHEMA.json to avoid asking repeated questions.")
    print(f"\nChanges logged to: {MASTER_LOG_PATH}")
    print("\nNext steps:")
    print("1. Review .MASTER_SCHEMA.json and fill in any missing information")
    print("2. Run schema_validator.py before document generation to ensure all required fields are present")
    print("3. As you generate more documents, run this script again to continue learning")


if __name__ == '__main__':
    main()
