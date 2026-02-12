#!/usr/bin/env python3
"""
Ninth Circuit Cover Page Generator
Uses CAPTION_NINTH.docx template and performs string replacement
"""

import sys
import shutil
from datetime import datetime
from zipfile import ZipFile
import os

def generate_cover(case_number, filing_name, judge_name, template_path="CAPTION_NINTH.docx"):
    """Generate cover page from template"""
    
    if not os.path.exists(template_path):
        print(f"ERROR: Template not found: {template_path}")
        return None
    
    # Create timestamp for output filename
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = f"COVER_PAGE_{timestamp}.docx"
    
    print(f"\nGenerating cover page...")
    print(f"  Case Number: {case_number}")
    print(f"  Filing Name: {filing_name}")
    print(f"  Judge: {judge_name}")
    
    # Copy template to output
    shutil.copy(template_path, output_file)
    
    # Unzip, modify XML, rezip
    with ZipFile(output_file, 'r') as zip_ref:
        zip_ref.extractall('temp_cover')
    
    # Read document.xml
    doc_xml_path = 'temp_cover/word/document.xml'
    with open(doc_xml_path, 'r', encoding='utf-8') as f:
        xml_content = f.read()
    
    # Perform replacements
    xml_content = xml_content.replace('[CASE_NUMBER]', case_number)
    xml_content = xml_content.replace('[FILING_NAME]', filing_name)
    xml_content = xml_content.replace('[JUDGE_NAME]', judge_name)
    
    # Write back
    with open(doc_xml_path, 'w', encoding='utf-8') as f:
        f.write(xml_content)
    
    # Rezip
    os.remove(output_file)
    with ZipFile(output_file, 'w') as zip_ref:
        for root, dirs, files in os.walk('temp_cover'):
            for file in files:
                file_path = os.path.join(root, file)
                arcname = file_path.replace('temp_cover/', '')
                zip_ref.write(file_path, arcname)
    
    # Cleanup
    shutil.rmtree('temp_cover')
    
    print(f"\n✓ Created: {output_file}")
    return output_file

def interactive_mode():
    """Interactive prompts for cover page generation"""
    print("\n" + "="*60)
    print("NINTH CIRCUIT COVER PAGE GENERATOR")
    print("="*60 + "\n")
    
    case_number = input("Case Number (e.g., 24-1234): ").strip()
    filing_name = input("Filing Name (e.g., APPELLANT'S OPENING BRIEF): ").strip().upper()
    judge_name = input("Judge Name (e.g., Hon. Susan Brnovich): ").strip()
    
    template = input("\nTemplate file (press Enter for CAPTION_NINTH.docx): ").strip()
    if not template:
        template = "CAPTION_NINTH.docx"
    
    output = generate_cover(case_number, filing_name, judge_name, template)
    
    if output:
        print(f"\n✓ Cover page ready: {output}")
        print("Copy this file to /mnt/user-data/outputs/ to download")

if __name__ == '__main__':
    if len(sys.argv) == 4:
        # Command line mode
        generate_cover(sys.argv[1], sys.argv[2], sys.argv[3])
    else:
        # Interactive mode
        interactive_mode()
