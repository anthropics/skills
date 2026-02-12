#!/usr/bin/env python3
"""
Integrated Cover Page Generator
Uses data from case_info.json instead of prompts
"""

import zipfile
import os
import shutil
from datetime import datetime
from pathlib import Path


class CoverGenerator:
    """Generate cover page from case data"""
    
    # Cover page XML template
    COVER_XML = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
<w:body>
    <!-- United States Court of Appeals Header -->
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:b/><w:sz w:val="28"/></w:rPr>
        <w:t>UNITED STATES COURT OF APPEALS</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:b/><w:sz w:val="28"/></w:rPr>
        <w:t>FOR THE NINTH CIRCUIT</w:t></w:r>
    </w:p>
    
    <!-- Case Number -->
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
        <w:r><w:rPr><w:b/><w:sz w:val="28"/></w:rPr>
        <w:t>{case_number}</w:t></w:r>
    </w:p>
    
    <!-- Parties -->
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="28"/></w:rPr>
        <w:t>{appellant}</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:i/><w:sz w:val="24"/></w:rPr>
        <w:t>Plaintiff-Appellant,</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="240"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="24"/></w:rPr>
        <w:t>v.</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="240"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="28"/></w:rPr>
        <w:t>{appellee}</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:i/><w:sz w:val="24"/></w:rPr>
        <w:t>Defendants-Appellees.</w:t></w:r>
    </w:p>
    
    <!-- Appeal From -->
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="24"/></w:rPr>
        <w:t>On Appeal from the {district_court}</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="24"/></w:rPr>
        <w:t>Case No. {district_case}</w:t></w:r>
    </w:p>
    <w:p>
        <w:pPr><w:jc w:val="center"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="24"/></w:rPr>
        <w:t>{judge_name}, District Judge</w:t></w:r>
    </w:p>
    
    <!-- Filing Type -->
    <w:p>
        <w:pPr><w:jc w:val="center"/><w:spacing w:before="720"/></w:pPr>
        <w:r><w:rPr><w:b/><w:sz w:val="32"/></w:rPr>
        <w:t>{filing_name}</w:t></w:r>
    </w:p>
    
    <!-- Counsel Block -->
    <w:p>
        <w:pPr><w:spacing w:before="1440"/></w:pPr>
        <w:r><w:rPr><w:sz w:val="24"/></w:rPr>
        <w:t>{counsel_name}</w:t></w:r>
    </w:p>
    <w:p>
        <w:r><w:rPr><w:i/><w:sz w:val="24"/></w:rPr>
        <w:t>{counsel_type}</w:t></w:r>
    </w:p>
    
    <w:sectPr>
        <w:pgSz w:w="12240" w:h="15840"/>
        <w:pgMar w:top="1440" w:right="1440" w:bottom="1440" w:left="1440"/>
    </w:sectPr>
</w:body>
</w:document>'''
    
    def __init__(self, case_number: str, filing_name: str, judge_name: str,
                 appellant: str, appellee: str, district_case: str,
                 district_court: str, counsel_name: str = None,
                 counsel_type: str = "Pro Se Appellant"):
        
        self.case_number = f"No. {case_number}" if case_number else "No. ____"
        self.filing_name = filing_name.upper()
        self.judge_name = judge_name if judge_name else "[District Judge Name]"
        self.appellant = appellant
        self.appellee = appellee
        self.district_case = district_case
        self.district_court = district_court
        self.counsel_name = counsel_name or appellant
        self.counsel_type = counsel_type
    
    def generate(self, output_path: Path) -> Path:
        """Generate cover page document"""
        
        # Fill in template
        xml_content = self.COVER_XML.format(
            case_number=self._escape_xml(self.case_number),
            appellant=self._escape_xml(self.appellant),
            appellee=self._escape_xml(self.appellee),
            district_court=self._escape_xml(self.district_court),
            district_case=self._escape_xml(self.district_case),
            judge_name=self._escape_xml(self.judge_name),
            filing_name=self._escape_xml(self.filing_name),
            counsel_name=self._escape_xml(self.counsel_name),
            counsel_type=self._escape_xml(self.counsel_type)
        )
        
        # Create docx
        self._create_docx(output_path, xml_content)
        
        return output_path
    
    def _escape_xml(self, text: str) -> str:
        """Escape XML special characters"""
        return (text.replace('&', '&amp;')
                    .replace('<', '&lt;')
                    .replace('>', '&gt;')
                    .replace('"', '&quot;')
                    .replace("'", '&apos;'))
    
    def _create_docx(self, output_path: Path, document_xml: str):
        """Create a .docx file from document XML"""
        
        temp_dir = Path("/tmp/cover_temp")
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        
        # Create directory structure
        (temp_dir / 'word').mkdir(parents=True)
        (temp_dir / '_rels').mkdir()
        (temp_dir / 'word' / '_rels').mkdir()
        
        # Write document.xml
        with open(temp_dir / 'word' / 'document.xml', 'w', encoding='utf-8') as f:
            f.write(document_xml)
        
        # Write [Content_Types].xml
        content_types = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
    <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
    <Default Extension="xml" ContentType="application/xml"/>
    <Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>
</Types>'''
        with open(temp_dir / '[Content_Types].xml', 'w', encoding='utf-8') as f:
            f.write(content_types)
        
        # Write _rels/.rels
        rels = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
    <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/>
</Relationships>'''
        with open(temp_dir / '_rels' / '.rels', 'w', encoding='utf-8') as f:
            f.write(rels)
        
        # Write word/_rels/document.xml.rels
        doc_rels = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
</Relationships>'''
        with open(temp_dir / 'word' / '_rels' / 'document.xml.rels', 'w', encoding='utf-8') as f:
            f.write(doc_rels)
        
        # Package as .docx
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as docx:
            for foldername, subfolders, filenames in os.walk(temp_dir):
                for filename in filenames:
                    file_path = Path(foldername) / filename
                    arcname = file_path.relative_to(temp_dir)
                    docx.write(file_path, arcname)
        
        shutil.rmtree(temp_dir)


def main():
    """Test cover generation"""
    generator = CoverGenerator(
        case_number="24-1234",
        filing_name="APPELLANT'S OPENING BRIEF",
        judge_name="Hon. Marco A. Hernández",
        appellant="TYLER ALLEN LOFALL",
        appellee="STATE OF OREGON, et al.",
        district_case="3:24-cv-00839-SB",
        district_court="United States District Court for the District of Oregon"
    )
    
    output = generator.generate(Path("test_cover.docx"))
    print(f"Generated: {output}")


if __name__ == "__main__":
    main()
