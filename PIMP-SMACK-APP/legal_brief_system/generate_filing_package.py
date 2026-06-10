#!/usr/bin/env python3
"""
Complete Legal Document Generator
Combines cover page + full brief into single filing package
"""

import os
import sys
import json
import shutil
from datetime import datetime
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from generate_brief import BriefAssembler, DataLoader


class FilingPackageGenerator:
    """Generate complete filing package: cover + brief"""
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
        self.data = DataLoader(data_dir)
        self.output_dir = self.data_dir.parent / "output"
        self.output_dir.mkdir(exist_ok=True)
    
    def generate_complete_package(self):
        """Generate cover page and brief as complete package"""
        
        case_info = self.data.load_case_info()
        
        print("\n" + "="*60)
        print("COMPLETE FILING PACKAGE GENERATOR")
        print("="*60)
        
        # Get case details
        case_num = case_info.get('case', {}).get('ninth_circuit_number', 'XX-XXXX')
        filing_type = case_info.get('filing', {}).get('type', 'BRIEF')
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        package_name = f"FILING_{case_num}_{timestamp}"
        
        # Create package directory
        package_dir = self.output_dir / package_name
        package_dir.mkdir(exist_ok=True)
        
        print(f"\nCreating filing package: {package_name}")
        print(f"Output directory: {package_dir}")
        
        # Generate components
        print("\n--- Generating Components ---")
        
        # 1. Cover Page
        print("  [1/3] Cover page...")
        cover_path = self._generate_cover(package_dir, case_info)
        
        # 2. Brief Body
        print("  [2/3] Brief body...")
        brief_path = self._generate_brief(package_dir)
        
        # 3. Filing checklist
        print("  [3/3] Filing checklist...")
        checklist_path = self._generate_checklist(package_dir, case_info)
        
        print("\n" + "="*60)
        print("✓ FILING PACKAGE COMPLETE")
        print("="*60)
        print(f"\nPackage location: {package_dir}")
        print("\nGenerated files:")
        print(f"  • {cover_path.name} - Cover page")
        print(f"  • {brief_path.name} - Brief body")
        print(f"  • {checklist_path.name} - Filing checklist")
        
        print("\n--- NEXT STEPS ---")
        print("  1. Open cover page and brief in Word")
        print("  2. Review and fill in argument sections")
        print("  3. Update TOC page numbers")
        print("  4. Add word count to certificate")
        print("  5. Export both to PDF")
        print("  6. Combine PDFs (cover first, then brief)")
        print("  7. File via CM/ECF")
        print("\n")
        
        return package_dir
    
    def _generate_cover(self, output_dir: Path, case_info: dict) -> Path:
        """Generate cover page"""
        from generate_cover_integrated import CoverGenerator
        
        generator = CoverGenerator(
            case_number=case_info.get('case', {}).get('ninth_circuit_number', ''),
            filing_name=case_info.get('filing', {}).get('type', 'APPELLANT\'S OPENING BRIEF'),
            judge_name=case_info.get('case', {}).get('lower_court_judge', ''),
            appellant=case_info.get('parties', {}).get('appellant', {}).get('name', ''),
            appellee=case_info.get('parties', {}).get('appellee', {}).get('name', ''),
            district_case=case_info.get('case', {}).get('district_court_number', ''),
            district_court=case_info.get('case', {}).get('district_court', '')
        )
        
        output_path = output_dir / "01_COVER_PAGE.docx"
        generator.generate(output_path)
        
        return output_path
    
    def _generate_brief(self, output_dir: Path) -> Path:
        """Generate brief body"""
        assembler = BriefAssembler(
            str(self.data_dir),
            str(self.data_dir.parent / "templates"),
            str(output_dir)
        )
        
        output_path = assembler.generate_docx("02_BRIEF_BODY.docx")
        return Path(output_path)
    
    def _generate_checklist(self, output_dir: Path, case_info: dict) -> Path:
        """Generate filing checklist"""
        
        case_num = case_info.get('case', {}).get('ninth_circuit_number', '')
        filing_type = case_info.get('filing', {}).get('type', '')
        
        checklist = f"""# FILING CHECKLIST
## {filing_type}
## Case No. {case_num}

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

---

## Pre-Filing Checklist

### Document Review
- [ ] Cover page has correct case number
- [ ] Cover page has correct filing type
- [ ] All parties correctly listed
- [ ] Judge name correct

### Brief Body
- [ ] Table of Contents page numbers updated
- [ ] Table of Authorities page numbers updated
- [ ] All argument sections completed
- [ ] All record citations include ER page numbers
- [ ] Certificate of Compliance word count filled in
- [ ] Certificate of Service date correct

### Formatting (FRAP 32)
- [ ] 14-point proportional font (Times New Roman)
- [ ] Double-spaced text
- [ ] 1-inch margins
- [ ] Page numbers on every page

### Word Count Limits
- Opening/Answering Brief: 14,000 words
- Reply Brief: 7,000 words
- [ ] Word count verified under limit

### Excerpts of Record
- [ ] ER prepared (if required)
- [ ] ER properly paginated
- [ ] All cited documents included

---

## Filing Steps

1. [ ] Export cover page to PDF
2. [ ] Export brief body to PDF
3. [ ] Combine PDFs (cover + brief)
4. [ ] Verify PDF is text-searchable
5. [ ] Log into CM/ECF
6. [ ] Select correct filing event
7. [ ] Upload combined PDF
8. [ ] Upload ER (if applicable)
9. [ ] Review NEF for accuracy
10. [ ] Save confirmation

---

## Key Deadlines

- Opening Brief: 40 days after docketing
- Answering Brief: 30 days after opening brief
- Reply Brief: 21 days after answering brief

---

## Contact Information

Ninth Circuit Clerk's Office: (415) 355-8000
CM/ECF Help Desk: (866) 233-7983

---

## Notes

[Add any case-specific notes here]

"""
        
        output_path = output_dir / "00_FILING_CHECKLIST.md"
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(checklist)
        
        return output_path


def main():
    """Main entry point"""
    
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"
    
    if not data_dir.exists():
        print(f"ERROR: Data directory not found: {data_dir}")
        print("Please ensure data files exist.")
        return
    
    generator = FilingPackageGenerator(str(data_dir))
    generator.generate_complete_package()


if __name__ == "__main__":
    main()
