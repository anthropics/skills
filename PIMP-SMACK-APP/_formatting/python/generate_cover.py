#!/usr/bin/env python3
"""
Ninth Circuit Cover Page Generator
Keeps the master template pristine and generates new covers by swapping placeholders
"""

import zipfile
import os
import shutil
from datetime import datetime

def prompt_for_values():
    """Prompt user for all placeholder values"""
    print("\n" + "="*60)
    print("NINTH CIRCUIT COVER PAGE GENERATOR")
    print("="*60 + "\n")
    
    # Case number (Ninth Circuit)
    print("Enter Ninth Circuit case number (or press Enter for blank):")
    print("  Example: 24-1234")
    case_number = input("  Case #: ").strip()
    if not case_number:
        case_number = "____________________"
    else:
        case_number = f"No. {case_number}"
    
    # Filing name
    print("\nEnter filing name:")
    print("  Examples:")
    print("    APPELLANT'S OPENING BRIEF")
    print("    APPELLANT'S REPLY BRIEF")
    print("    MOTION FOR STAY PENDING APPEAL")
    filing_name = input("  Filing: ").strip().upper()
    if not filing_name:
        filing_name = "APPELLANT'S OPENING BRIEF"
    
    # Judge name
    print("\nEnter district judge name (or press Enter for placeholder):")
    print("  Example: Stacy Beckerman")
    judge_name = input("  Judge: ").strip()
    if not judge_name:
        judge_name = "[District Judge Name]"
    else:
        judge_name = f"Hon. {judge_name}"
    
    print("\n" + "="*60)
    print("GENERATING COVER PAGE...")
    print("="*60 + "\n")
    
    return {
        'case_number': case_number,
        'filing_name': filing_name,
        'judge_name': judge_name
    }

def generate_cover(template_path, output_path, values):
    """
    Generate a new cover page from the template by replacing placeholders
    
    Args:
        template_path: Path to the master template (TEMPLATE_CAPTION.docx)
        output_path: Path for the generated file
        values: Dictionary with placeholder values
    """
    
    # Create a temporary directory for extraction
    temp_dir = "/tmp/cover_temp"
    if os.path.exists(temp_dir):
        shutil.rmtree(temp_dir)
    os.makedirs(temp_dir)
    
    # Extract the template docx (it's a ZIP file)
    with zipfile.ZipFile(template_path, 'r') as zip_ref:
        zip_ref.extractall(temp_dir)
    
    # Read the document.xml
    doc_xml_path = os.path.join(temp_dir, 'word', 'document.xml')
    with open(doc_xml_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Replace placeholders
    # Case number
    content = content.replace('No. 6461', values['case_number'])
    
    # Filing name (in FILLIN field)
    content = content.replace('APPELLANTS OPENING BRIEF', values['filing_name'])
    
    # Judge name
    content = content.replace('Hon. Stacy Beckerman', values['judge_name'])
    
    # Write back the modified XML
    with open(doc_xml_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    # Re-package as a .docx file
    with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as docx:
        for foldername, subfolders, filenames in os.walk(temp_dir):
            for filename in filenames:
                file_path = os.path.join(foldername, filename)
                arcname = os.path.relpath(file_path, temp_dir)
                docx.write(file_path, arcname)
    
    # Clean up temp directory
    shutil.rmtree(temp_dir)
    
    print(f"✓ Cover page generated: {output_path}")
    print(f"  Case Number: {values['case_number']}")
    print(f"  Filing Name: {values['filing_name']}")
    print(f"  Judge: {values['judge_name']}")

def main():
    """Main function"""
    
    # Path to the master template (READ-ONLY)
    template_path = "TEMPLATE_CAPTION.docx"
    
    # Check if template exists
    if not os.path.exists(template_path):
        print(f"ERROR: Template not found: {template_path}")
        print("Please ensure TEMPLATE_CAPTION.docx is in the current directory.")
        return
    
    # Get values from user
    values = prompt_for_values()
    
    # Generate output filename
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_filename = f"COVER_PAGE_{timestamp}.docx"
    
    # Generate the new cover page
    generate_cover(template_path, output_filename, values)
    
    print(f"\n{'='*60}")
    print("DONE! Your cover page is ready.")
    print(f"{'='*60}\n")
    print(f"Output file: {output_filename}")
    print("\nNext steps:")
    print("  1. Open the file to verify it looks correct")
    print("  2. Export to PDF")
    print("  3. Combine with your body text PDF")
    print("  4. File with Ninth Circuit\n")

if __name__ == "__main__":
    main()
