#!/usr/bin/env python3
"""
Ninth Circuit Legal Brief Generator
Automated document creation system - No Word dependency
Generates complete briefs from JSON data files
"""

import argparse
import json
import os
import stat
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional
import zipfile
import shutil

# ============================================================================
# CONFIGURATION
# ============================================================================

class BriefConfig:
    """Brief formatting configuration per FRAP rules"""
    
    # Font settings (14pt proportional, serif)
    FONT_FAMILY = "Times New Roman"
    FONT_SIZE = 28  # Word XML uses half-points (28 = 14pt)
    FONT_SIZE_FOOTNOTE = 28  # Same size for footnotes per FRAP
    
    # Margins (1 inch = 1440 twips)
    MARGIN_TOP = 1440
    MARGIN_BOTTOM = 1440
    MARGIN_LEFT = 1440
    MARGIN_RIGHT = 1440
    
    # Line spacing (double = 480, 1.5 = 360)
    LINE_SPACING_DOUBLE = 480
    LINE_SPACING_SINGLE = 240
    
    # Page numbering
    PAGE_NUM_POSITION = "bottom"


# ============================================================================
# DATA LOADERS
# ============================================================================

class DataLoader:
    """Load all JSON data files"""
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
    
    def load_case_info(self) -> dict:
        return self._load_json("case_info.json")
    
    def load_issues(self) -> dict:
        return self._load_json("issues_presented.json")
    
    def load_authorities(self) -> dict:
        return self._load_json("authorities.json")
    
    def load_timeline(self) -> dict:
        return self._load_json("timeline.json")
    
    def load_arguments(self) -> dict:
        return self._load_json("arguments.json")

    def load_argument_content(self) -> dict:
        return self._load_json("argument_content.json")

    def load_evidence_pool(self) -> dict:
        return self._load_json("evidence_pool.json")
    
    def _load_json(self, filename: str) -> dict:
        path = self.data_dir / filename
        if path.exists():
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}


# ============================================================================
# XML GENERATORS
# ============================================================================

class XMLGenerator:
    """Generate Word XML content"""
    
    NS = {
        'w': 'http://schemas.openxmlformats.org/wordprocessingml/2006/main',
        'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
    }
    
    @staticmethod
    def paragraph(text: str, style: str = "Normal", bold: bool = False, 
                  italic: bool = False, centered: bool = False,
                  spacing_after: int = 0) -> str:
        """Generate a paragraph element"""
        
        align = '<w:jc w:val="center"/>' if centered else ''
        spacing = f'<w:spacing w:after="{spacing_after}" w:line="{BriefConfig.LINE_SPACING_DOUBLE}" w:lineRule="auto"/>' if spacing_after else f'<w:spacing w:line="{BriefConfig.LINE_SPACING_DOUBLE}" w:lineRule="auto"/>'
        
        run_props = []
        if bold:
            run_props.append('<w:b/>')
        if italic:
            run_props.append('<w:i/>')
        
        run_props_xml = ''.join(run_props)
        if run_props_xml:
            run_props_xml = f'<w:rPr>{run_props_xml}</w:rPr>'
        
        # Escape XML special characters
        text = text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        
        return f'''<w:p>
            <w:pPr>
                <w:pStyle w:val="{style}"/>
                {align}
                {spacing}
            </w:pPr>
            <w:r>
                {run_props_xml}
                <w:t xml:space="preserve">{text}</w:t>
            </w:r>
        </w:p>'''
    
    @staticmethod
    def heading(text: str, level: int = 1) -> str:
        """Generate a heading element"""
        style = f"Heading{level}"
        bold = level <= 2
        
        text = text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        
        return f'''<w:p>
            <w:pPr>
                <w:pStyle w:val="{style}"/>
                <w:spacing w:before="240" w:after="120"/>
            </w:pPr>
            <w:r>
                <w:rPr>{'<w:b/>' if bold else ''}</w:rPr>
                <w:t xml:space="preserve">{text}</w:t>
            </w:r>
        </w:p>'''
    
    @staticmethod
    def page_break() -> str:
        """Generate a page break"""
        return '''<w:p>
            <w:r>
                <w:br w:type="page"/>
            </w:r>
        </w:p>'''
    
    @staticmethod  
    def toc_entry(text: str, page: str, level: int = 1) -> str:
        """Generate a TOC entry with leader dots"""
        indent = level * 720  # 0.5 inch per level
        
        text = text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        
        return f'''<w:p>
            <w:pPr>
                <w:tabs>
                    <w:tab w:val="right" w:leader="dot" w:pos="9360"/>
                </w:tabs>
                <w:ind w:left="{indent}"/>
            </w:pPr>
            <w:r>
                <w:t>{text}</w:t>
            </w:r>
            <w:r>
                <w:tab/>
            </w:r>
            <w:r>
                <w:t>{page}</w:t>
            </w:r>
        </w:p>'''


# ============================================================================
# SECTION GENERATORS
# ============================================================================

class SectionGenerator:
    """Generate individual brief sections from exact source data"""

    def __init__(self, data_loader: DataLoader):
        self.data = data_loader
        self.xml = XMLGenerator()
        self.argument_content = self.data.load_argument_content() or {}
        self.evidence_pool = self.data.load_evidence_pool() or {}

    def _split_paragraphs(self, text: str) -> List[str]:
        return [block.strip() for block in text.split('\n\n') if block.strip()]

    def _facts_for_section(self, section_key: str) -> List[Dict]:
        facts = self.evidence_pool.get('facts', [])
        selected = [fact for fact in facts if section_key in fact.get('used_in_sections', [])]
        return sorted(selected, key=lambda x: x.get('date', ''))

    def _fact_paragraphs(self, facts: List[Dict]) -> List[str]:
        paragraphs = []
        for fact in facts:
            statement = fact.get('statement', '').strip()
            cite = fact.get('record_cite')
            if not statement:
                continue
            text = statement
            if cite:
                text += f" ({cite}.)"
            paragraphs.append(self.xml.paragraph(text, spacing_after=240))
        return paragraphs

    def _argument_text(self, roman: str, letter: Optional[str] = None) -> str:
        content_sections = self.argument_content.get('content_sections', {})
        argument_sections = content_sections.get('arguments', {})
        if letter:
            return argument_sections.get(roman, {}).get(letter, {}).get('content', '').strip()
        return argument_sections.get(roman, {}).get('content', '').strip()

    def _introduction_text(self) -> str:
        content_sections = self.argument_content.get('content_sections', {})
        return content_sections.get('introduction', {}).get('content', '').strip()

    def _summary_text(self) -> str:
        content_sections = self.argument_content.get('content_sections', {})
        return content_sections.get('summary_of_argument', {}).get('content', '').strip()

    def generate_disclosure_statement(self) -> str:
        case_info = self.data.load_case_info()
        party = case_info.get('parties', {}).get('appellant', {})
        xml_parts = [self.xml.heading("DISCLOSURE STATEMENT", 1)]
        if party.get('pro_se'):
            xml_parts.append(self.xml.paragraph(
                "Appellant is a natural person proceeding pro se and is not required to file a disclosure statement pursuant to FRAP 26.1.",
                spacing_after=240
            ))
        else:
            disclosure = case_info.get('disclosure_statement', {}).get('text', '')
            if disclosure:
                for block in self._split_paragraphs(disclosure):
                    xml_parts.append(self.xml.paragraph(block, spacing_after=240))
            else:
                xml_parts.append(self.xml.paragraph(
                    "[Insert disclosure statement per FRAP 26.1]",
                    spacing_after=240
                ))
        return '\n'.join(xml_parts)

    def generate_table_of_contents(self) -> str:
        xml_parts = [
            self.xml.heading("TABLE OF CONTENTS", 1),
            self.xml.paragraph("Page", centered=True, bold=True),
        ]
        sections = [
            ("DISCLOSURE STATEMENT", "i", 1),
            ("TABLE OF AUTHORITIES", "iv", 1),
            ("INTRODUCTION", "1", 1),
            ("JURISDICTIONAL STATEMENT", "2", 1),
            ("ISSUES PRESENTED", "3", 1),
            ("STATEMENT OF THE CASE", "4", 1),
            ("SUMMARY OF THE ARGUMENT", "5", 1),
            ("STANDARD OF REVIEW", "6", 1),
            ("ARGUMENT", "7", 1),
        ]
        arguments = self.data.load_arguments()
        for arg in arguments.get('arguments', []):
            sections.append((f"{arg['number']}. {arg['heading']}", "X", 2))
            for sub in arg.get('subarguments', []):
                sections.append((f"{sub['letter']}. {sub['heading']}", "X", 3))
        sections.extend([
            ("CONCLUSION", "X", 1),
            ("STATEMENT OF RELATED CASES", "X", 1),
            ("CERTIFICATE OF COMPLIANCE", "X", 1),
            ("CERTIFICATE OF SERVICE", "X", 1),
        ])
        for text, page, level in sections:
            xml_parts.append(self.xml.toc_entry(text, page, level))
        return '\n'.join(xml_parts)

    def generate_table_of_authorities(self) -> str:
        auth = self.data.load_authorities()
        xml_parts = [
            self.xml.heading("TABLE OF AUTHORITIES", 1),
            self.xml.paragraph("Page(s)", centered=True, bold=True),
        ]
        xml_parts.append(self.xml.paragraph("Cases", bold=True, spacing_after=120))
        cases = sorted(auth.get('cases', []), key=lambda x: x['name'])
        for case in cases:
            pages = ', '.join(str(p) for p in case.get('pages_cited', [])) or "i"
            xml_parts.append(self.xml.toc_entry(case.get('bluebook', case.get('name', '')), pages, level=1))
        xml_parts.append(self.xml.paragraph(""))
        xml_parts.append(self.xml.paragraph("Statutes", bold=True, spacing_after=120))
        for statute in auth.get('statutes', []):
            pages = ', '.join(str(p) for p in statute.get('pages_cited', [])) or "i"
            xml_parts.append(self.xml.toc_entry(statute.get('bluebook', ''), pages, level=1))
        xml_parts.append(self.xml.paragraph(""))
        xml_parts.append(self.xml.paragraph("Rules", bold=True, spacing_after=120))
        for rule in auth.get('rules', []):
            pages = ', '.join(str(p) for p in rule.get('pages_cited', [])) or "i"
            xml_parts.append(self.xml.toc_entry(rule.get('bluebook', ''), pages, level=1))
        xml_parts.append(self.xml.paragraph(""))
        xml_parts.append(self.xml.paragraph("Constitutional Provisions", bold=True, spacing_after=120))
        for provision in auth.get('constitutional_provisions', []):
            pages = ', '.join(str(p) for p in provision.get('pages_cited', [])) or "i"
            xml_parts.append(self.xml.toc_entry(provision.get('bluebook', ''), pages, level=1))
        return '\n'.join(xml_parts)

    def generate_introduction(self) -> str:
        xml_parts = [self.xml.heading("INTRODUCTION", 1)]
        intro_text = self._introduction_text()
        if intro_text:
            for block in self._split_paragraphs(intro_text):
                xml_parts.append(self.xml.paragraph(block, spacing_after=240))
        else:
            xml_parts.append(self.xml.paragraph("[Draft introduction text in argument_content.json]", spacing_after=240))
        return '\n'.join(xml_parts)

    def generate_jurisdictional_statement(self) -> str:
        case_info = self.data.load_case_info()
        juris = case_info.get('jurisdiction', {})
        xml_parts = [self.xml.heading("JURISDICTIONAL STATEMENT", 1)]
        xml_parts.append(self.xml.paragraph(
            f"The district court had jurisdiction pursuant to {juris.get('district_court_basis', '28 U.S.C. § 1331')}.",
            spacing_after=240
        ))
        xml_parts.append(self.xml.paragraph(
            f"This Court has jurisdiction pursuant to {juris.get('appeals_court_basis', '28 U.S.C. § 1291')}.",
            spacing_after=240
        ))
        xml_parts.append(self.xml.paragraph(
            f"The district court entered its final judgment on {juris.get('judgment_date', '[DATE]')}. "
            f"Appellant timely filed a notice of appeal on {juris.get('notice_of_appeal_date', '[DATE]')} "
            f"pursuant to {juris.get('timeliness_rule', 'FRAP 4(a)(1)(A)')}.",
            spacing_after=240
        ))
        if juris.get('final_judgment'):
            xml_parts.append(self.xml.paragraph(
                "The appeal is from a final order disposing of all parties' claims.",
                spacing_after=240
            ))
        return '\n'.join(xml_parts)

    def generate_issues_presented(self) -> str:
        issues = self.data.load_issues()
        xml_parts = [self.xml.heading("ISSUES PRESENTED", 1)]
        for issue in issues.get('issues', []):
            xml_parts.append(self.xml.paragraph(
                f"{issue['number']}. {issue['issue_statement']}",
                spacing_after=240
            ))
        return '\n'.join(xml_parts)

    def generate_statement_of_case(self) -> str:
        xml_parts = [self.xml.heading("STATEMENT OF THE CASE", 1)]
        facts = self._facts_for_section('statement_of_case')
        if facts:
            xml_parts.extend(self._fact_paragraphs(facts))
            return '\n'.join(xml_parts)
        timeline = self.data.load_timeline()
        for event in timeline.get('events', []):
            cite = f" ({event['er_cite']})" if event.get('er_cite') else ""
            xml_parts.append(self.xml.paragraph(
                f"On {event['date']}, {event['event']}.{cite}",
                spacing_after=240
            ))
        return '\n'.join(xml_parts)

    def generate_summary_of_argument(self) -> str:
        xml_parts = [self.xml.heading("SUMMARY OF THE ARGUMENT", 1)]
        summary = self._summary_text()
        if summary:
            for block in self._split_paragraphs(summary):
                xml_parts.append(self.xml.paragraph(block, spacing_after=240))
        else:
            xml_parts.append(self.xml.paragraph("[Draft summary text in argument_content.json]", spacing_after=240))
        return '\n'.join(xml_parts)

    def generate_standards_of_review(self) -> str:
        issues = self.data.load_issues()
        xml_parts = [self.xml.heading("STANDARD OF REVIEW", 1)]
        standards = {}
        for issue in issues.get('issues', []):
            std = issue.get('standard_of_review', 'de novo')
            if std not in standards:
                standards[std] = {
                    'citation': issue.get('standard_citation', ''),
                    'issues': []
                }
            standards[std]['issues'].append(issue['heading'])
        for std, info in standards.items():
            xml_parts.append(self.xml.paragraph(
                f"This Court reviews {', '.join(info['issues'])} {std}. {info['citation']}",
                spacing_after=240
            ))
        return '\n'.join(xml_parts)

    def generate_argument_structure(self) -> str:
        arguments = self.data.load_arguments()
        xml_parts = [self.xml.heading("ARGUMENT", 1)]
        for arg in arguments.get('arguments', []):
            roman = arg.get('number', '')
            heading = arg.get('heading', '')
            xml_parts.append(self.xml.heading(f"{roman}. {heading}", level=2))
            base_text = self._argument_text(roman)
            if base_text:
                for block in self._split_paragraphs(base_text):
                    xml_parts.append(self.xml.paragraph(block, spacing_after=240))
            else:
                xml_parts.append(self.xml.paragraph(f"[Insert argument text for {heading}]", spacing_after=240))
            xml_parts.extend(self._fact_paragraphs(self._facts_for_section(f"argument_{roman}")))
            for sub in arg.get('subarguments', []):
                letter = sub.get('letter', '')
                sub_heading = sub.get('heading', '')
                xml_parts.append(self.xml.heading(f"{letter}. {sub_heading}", level=3))
                sub_text = self._argument_text(roman, letter)
                if sub_text:
                    for block in self._split_paragraphs(sub_text):
                        xml_parts.append(self.xml.paragraph(block, spacing_after=240))
                else:
                    xml_parts.append(self.xml.paragraph(f"[Insert argument text for {sub_heading}]", spacing_after=240))
                xml_parts.extend(self._fact_paragraphs(self._facts_for_section(f"argument_{roman}_{letter}")))
                citations = sub.get('citations')
                if citations:
                    xml_parts.append(self.xml.paragraph(f"Authorities: {', '.join(citations)}", spacing_after=240))
        return '\n'.join(xml_parts)

    def generate_conclusion(self) -> str:
        case_info = self.data.load_case_info()
        conclusion_text = case_info.get('conclusion', {}).get('text')
        xml_parts = [self.xml.heading("CONCLUSION", 1)]
        if conclusion_text:
            for block in self._split_paragraphs(conclusion_text):
                xml_parts.append(self.xml.paragraph(block, spacing_after=480))
        else:
            xml_parts.append(self.xml.paragraph(
                "For the foregoing reasons, Appellant respectfully requests that this Court reverse the district court's judgment and remand for further proceedings.",
                spacing_after=480
            ))
        counsel = case_info.get('counsel', {}).get('appellant_counsel', {})
        xml_parts.extend([
            self.xml.paragraph(f"Dated: {datetime.now().strftime('%B %d, %Y')}", spacing_after=240),
            self.xml.paragraph("Respectfully submitted,", spacing_after=480),
            self.xml.paragraph(f"/s/ {counsel.get('name', '[Name]')}", spacing_after=120),
            self.xml.paragraph(counsel.get('name', '[Name]'), spacing_after=120),
        ])
        if counsel.get('pro_se'):
            xml_parts.append(self.xml.paragraph("Pro Se Appellant"))
        else:
            xml_parts.append(self.xml.paragraph("Attorney for Appellant"))
        return '\n'.join(xml_parts)

    def generate_certificate_of_compliance(self) -> str:
        case_info = self.data.load_case_info()
        counsel = case_info.get('counsel', {}).get('appellant_counsel', {})
        xml_parts = [
            self.xml.heading("CERTIFICATE OF COMPLIANCE", 1),
            self.xml.paragraph(
                "Pursuant to Federal Rule of Appellate Procedure 32(g), I certify that this brief:",
                spacing_after=240
            ),
            self.xml.paragraph(
                "1. Complies with the type-volume limitation of FRAP 32(a)(7)(B) because this brief contains [WORD COUNT] words, excluding the parts of the brief exempted by FRAP 32(f).",
                spacing_after=240
            ),
            self.xml.paragraph(
                "2. Complies with the typeface requirements of FRAP 32(a)(5) and the type-style requirements of FRAP 32(a)(6) because this brief has been prepared in a proportionally spaced typeface using Microsoft Word in 14-point Times New Roman.",
                spacing_after=480
            ),
            self.xml.paragraph(f"Dated: {datetime.now().strftime('%B %d, %Y')}", spacing_after=480),
            self.xml.paragraph(f"/s/ {counsel.get('name', '[Name]')}", spacing_after=120),
        ]
        return '\n'.join(xml_parts)

    def generate_certificate_of_service(self) -> str:
        case_info = self.data.load_case_info()
        counsel = case_info.get('counsel', {}).get('appellant_counsel', {})
        xml_parts = [
            self.xml.heading("CERTIFICATE OF SERVICE", 1),
            self.xml.paragraph(
                f"I hereby certify that on {datetime.now().strftime('%B %d, %Y')}, I electronically filed the foregoing brief with the Clerk of Court using the CM/ECF system, which will send notification of such filing to all counsel of record.",
                spacing_after=480
            ),
            self.xml.paragraph(f"/s/ {counsel.get('name', '[Name]')}", spacing_after=120),
        ]
        return '\n'.join(xml_parts)

    def generate_related_cases(self) -> str:
        case_info = self.data.load_case_info()
        related = case_info.get('related_cases', [])
        xml_parts = [self.xml.heading("STATEMENT OF RELATED CASES", 1)]
        if related:
            for case in related:
                xml_parts.append(self.xml.paragraph(case, spacing_after=240))
        else:
            xml_parts.append(self.xml.paragraph("Appellant is unaware of any related cases pending in this Court."))
        return '\n'.join(xml_parts)
# ============================================================================
# DOCUMENT ASSEMBLER
# ============================================================================

class BriefAssembler:
    """Assemble complete brief from sections"""
    
    def __init__(self, data_dir: str, template_dir: str, output_dir: str):
        self.data_dir = Path(data_dir)
        self.template_dir = Path(template_dir)
        self.output_dir = Path(output_dir)
        
        self.data = DataLoader(data_dir)
        self.sections = SectionGenerator(self.data)
    
    def assemble_brief(self) -> str:
        """Assemble all sections into complete document XML"""
        
        sections = [
            self.sections.generate_disclosure_statement(),
            XMLGenerator.page_break(),
            self.sections.generate_table_of_contents(),
            XMLGenerator.page_break(),
            self.sections.generate_table_of_authorities(),
            XMLGenerator.page_break(),
            self.sections.generate_introduction(),
            XMLGenerator.page_break(),
            self.sections.generate_jurisdictional_statement(),
            XMLGenerator.page_break(),
            self.sections.generate_issues_presented(),
            XMLGenerator.page_break(),
            self.sections.generate_statement_of_case(),
            XMLGenerator.page_break(),
            self.sections.generate_summary_of_argument(),
            XMLGenerator.page_break(),
            self.sections.generate_standards_of_review(),
            XMLGenerator.page_break(),
            self.sections.generate_argument_structure(),
            XMLGenerator.page_break(),
            self.sections.generate_conclusion(),
            XMLGenerator.page_break(),
            self.sections.generate_related_cases(),
            XMLGenerator.page_break(),
            self.sections.generate_certificate_of_compliance(),
            XMLGenerator.page_break(),
            self.sections.generate_certificate_of_service(),
        ]
        
        return '\n'.join(sections)
    
    def create_document_xml(self) -> str:
        """Create complete document.xml content"""
        
        body_content = self.assemble_brief()
        
        return f'''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"
            xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
    <w:body>
        {body_content}
        <w:sectPr>
            <w:pgSz w:w="12240" w:h="15840"/>
            <w:pgMar w:top="{BriefConfig.MARGIN_TOP}" 
                     w:right="{BriefConfig.MARGIN_RIGHT}" 
                     w:bottom="{BriefConfig.MARGIN_BOTTOM}" 
                     w:left="{BriefConfig.MARGIN_LEFT}"/>
            <w:pgNumType w:start="1"/>
        </w:sectPr>
    </w:body>
</w:document>'''
    
    def generate_docx(self, output_filename: str = None) -> str:
        """Generate complete .docx file"""
        
        if output_filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_filename = f"BRIEF_{timestamp}.docx"
        
        output_path = self.output_dir / output_filename
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Check for template
        template_path = self.template_dir / "BRIEF_TEMPLATE.docx"
        
        if template_path.exists():
            # Use existing template
            self._generate_from_template(template_path, output_path)
        else:
            # Create from scratch
            self._generate_from_scratch(output_path)
        
        return str(output_path)
    
    def _generate_from_template(self, template_path: Path, output_path: Path):
        """Generate document using existing template"""
        
        temp_dir = Path("/tmp/brief_temp")
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        temp_dir.mkdir(parents=True)
        
        # Extract template
        with zipfile.ZipFile(template_path, 'r') as zip_ref:
            zip_ref.extractall(temp_dir)
        
        # Replace document.xml
        doc_xml_path = temp_dir / 'word' / 'document.xml'
        with open(doc_xml_path, 'w', encoding='utf-8') as f:
            f.write(self.create_document_xml())
        
        # Re-package
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as docx:
            for foldername, subfolders, filenames in os.walk(temp_dir):
                for filename in filenames:
                    file_path = Path(foldername) / filename
                    arcname = file_path.relative_to(temp_dir)
                    docx.write(file_path, arcname)
        
        shutil.rmtree(temp_dir)
    
    def _generate_from_scratch(self, output_path: Path):
        """Generate document without template (basic structure)"""
        
        temp_dir = Path("/tmp/brief_temp")
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        
        # Create directory structure
        (temp_dir / 'word').mkdir(parents=True)
        (temp_dir / '_rels').mkdir()
        (temp_dir / 'word' / '_rels').mkdir()
        
        # Write document.xml
        with open(temp_dir / 'word' / 'document.xml', 'w', encoding='utf-8') as f:
            f.write(self.create_document_xml())
        
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
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as docx:
            for foldername, subfolders, filenames in os.walk(temp_dir):
                for filename in filenames:
                    file_path = Path(foldername) / filename
                    arcname = file_path.relative_to(temp_dir)
                    docx.write(file_path, arcname)
        
        shutil.rmtree(temp_dir)


# ============================================================================
# OUTBOX HANDOFF
# ============================================================================

def dispatch_to_outbox(docx_path: Path, case_info: Dict, outbox_dir: Path) -> Optional[tuple]:
    """Copy generated DOCX into OUTBOX/briefs and OUTBOX/chronological"""

    outbox_dir = Path(outbox_dir)
    briefs_dir = outbox_dir / "briefs"
    chrono_dir = outbox_dir / "chronological"
    briefs_dir.mkdir(parents=True, exist_ok=True)
    chrono_dir.mkdir(parents=True, exist_ok=True)

    case_number = case_info.get('case', {}).get('ninth_circuit_number', 'XX-XXXX')
    filing_type = case_info.get('filing', {}).get('type', 'BRIEF_BODY')
    safe_case = case_number.replace(' ', '').replace('/', '-')
    safe_filing = filing_type.replace(' ', '_').upper()
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    primary_name = f"{safe_case}-{safe_filing}-{timestamp}.docx"
    primary_path = briefs_dir / primary_name
    shutil.copy2(docx_path, primary_path)

    chrono_name = f"{timestamp}-{safe_case}-{safe_filing}.docx"
    chrono_path = chrono_dir / chrono_name
    shutil.copy2(docx_path, chrono_path)
    os.chmod(chrono_path, stat.S_IREAD)

    return primary_path, chrono_path


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

def main():
    """Main entry point"""

    parser = argparse.ArgumentParser(description="Generate Ninth Circuit brief body from JSON data")
    script_dir = Path(__file__).parent
    parser.add_argument("--data-dir", default=str(script_dir / "data"), help="Path to data directory")
    parser.add_argument("--template-dir", default=str(script_dir / "templates"), help="Path to template directory")
    parser.add_argument("--output-dir", default=str(script_dir / "output"), help="Directory for generated DOCX")
    parser.add_argument("--outbox-dir", default=str(script_dir.parent / "OUTBOX"), help="Root OUTBOX directory for dual copies")
    parser.add_argument("--skip-outbox", action="store_true", help="Skip copying the result into OUTBOX")
    args = parser.parse_args()

    data_dir = Path(args.data_dir)
    template_dir = Path(args.template_dir)
    output_dir = Path(args.output_dir)

    print("\n" + "="*60)
    print("NINTH CIRCUIT BRIEF GENERATOR")
    print("="*60 + "\n")

    required_files = [
        "case_info.json",
        "issues_presented.json",
        "authorities.json",
        "timeline.json",
        "arguments.json",
        "argument_content.json",
        "evidence_pool.json",
    ]
    missing = [f for f in required_files if not (data_dir / f).exists()]
    if missing:
        print("ERROR: Missing data files:")
        for f in missing:
            print(f"  - {f}")
        print(f"\nPlease ensure all data files exist in: {data_dir}")
        return

    assembler = BriefAssembler(str(data_dir), str(template_dir), str(output_dir))

    print("Generating brief from data files...")
    print(f"  Data directory: {data_dir}")

    generated_path = Path(assembler.generate_docx())
    print(f"\n✓ Brief generated: {generated_path}")

    if not args.skip_outbox:
        case_info = assembler.data.load_case_info()
        outbox_dir = Path(args.outbox_dir)
        primary_path, chrono_path = dispatch_to_outbox(generated_path, case_info, outbox_dir)
        print(f"✓ Copied to OUTBOX: {primary_path}")
        print(f"✓ Chronological copy (read-only): {chrono_path}")
    else:
        print("(Skipped OUTBOX copy)")

    print("\nNext steps:")
    print("  1. Review every section to confirm citations and quotes")
    print("  2. Update the TOC page numbers after pagination")
    print("  3. Insert the final word count in the certificate of compliance")
    print("  4. Export to PDF and merge with the cover page for filing")


if __name__ == "__main__":
    main()
