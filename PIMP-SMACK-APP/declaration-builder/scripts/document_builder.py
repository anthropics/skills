#!/usr/bin/env python3
"""
Document Builder for Pro Se Domination
Pure Python implementation - NO subprocess calls

Builds legal documents via direct XML manipulation and zipfile packing.
Uses template-based approach with placeholder resolution.

Author: Tyler 'Oooo-pus Pimp-Daddy' Lofall & Claude (A-Team Productions)
"""

import os
import io
import zipfile
from datetime import datetime
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from xml.sax.saxutils import escape as xml_escape


# ============================================================================
# DATA CLASSES
# ============================================================================

@dataclass
class DeclarationFact:
    """A single fact in a declaration with 2+2+1 structure."""
    title: str
    circumstance_time_place: str
    circumstance_parties: str
    element_primary: str
    element_supporting: str
    party_link: str
    defendant: str = "Defendants"
    witnesses: List[str] = field(default_factory=list)
    evidence_uids: List[str] = field(default_factory=list)


@dataclass
class JurisdictionConfig:
    """Configuration for a specific jurisdiction."""
    circuit: str
    font_name: str = "Century Schoolbook"
    font_size: int = 14  # in half-points, so 28 = 14pt
    line_spacing: int = 480  # in twentieths of a point, 480 = double
    margins: Dict[str, int] = field(default_factory=lambda: {
        "top": 1440, "bottom": 1440, "left": 1440, "right": 1440  # 1440 twips = 1 inch
    })
    word_limit: int = 14000
    special_rules: List[str] = field(default_factory=list)


# ============================================================================
# JURISDICTION DATABASE
# ============================================================================

JURISDICTIONS = {
    "ninth": JurisdictionConfig(
        circuit="NINTH",
        font_name="Californian FB",
        font_size=28,  # 14pt
        line_spacing=480,
        special_rules=[
            "Circuit Rule 28-2.1: Cover must include case number and short title",
            "Circuit Rule 32-1: 14-point font for text",
        ]
    ),
    "first": JurisdictionConfig(
        circuit="FIRST",
        font_name="Californian FB",
        font_size=28,
        special_rules=[
            "Local Rule 28.0: Corporate disclosure required",
        ]
    ),
    "dc": JurisdictionConfig(
        circuit="DC",
        font_name="Californian FB",
        font_size=28,
        special_rules=[
            "Circuit Rule 28(a)(1): Glossary required for acronym-heavy cases",
            "Circuit Rule 32(a)(1): 8 paper copies required within 2 days",
        ]
    ),
    # Add more circuits as needed
}


# ============================================================================
# XML TEMPLATES
# ============================================================================

DOCUMENT_XML_TEMPLATE = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"
            xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"
            xmlns:wp="http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing"
            xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main">
  <w:body>
{CONTENT}
    <w:sectPr>
      <w:pgSz w:w="12240" w:h="15840"/>
      <w:pgMar w:top="{MARGIN_TOP}" w:right="{MARGIN_RIGHT}" w:bottom="{MARGIN_BOTTOM}" w:left="{MARGIN_LEFT}" w:header="720" w:footer="720"/>
    </w:sectPr>
  </w:body>
</w:document>'''

STYLES_XML = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:styles xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
  <w:docDefaults>
    <w:rPrDefault>
      <w:rPr>
        <w:rFonts w:ascii="{FONT}" w:hAnsi="{FONT}"/>
        <w:sz w:val="{FONT_SIZE}"/>
      </w:rPr>
    </w:rPrDefault>
    <w:pPrDefault>
      <w:pPr>
        <w:spacing w:line="{LINE_SPACING}" w:lineRule="auto"/>
      </w:pPr>
    </w:pPrDefault>
  </w:docDefaults>
  
  <w:style w:type="paragraph" w:styleId="Normal" w:default="1">
    <w:name w:val="Normal"/>
  </w:style>
  
  <w:style w:type="paragraph" w:styleId="Heading1">
    <w:name w:val="heading 1"/>
    <w:pPr>
      <w:spacing w:before="480" w:after="240"/>
      <w:jc w:val="center"/>
      <w:outlineLvl w:val="0"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="{FONT}" w:hAnsi="{FONT}"/>
      <w:b/><w:bCs/>
      <w:sz w:val="28"/><w:szCs w:val="28"/>
    </w:rPr>
  </w:style>

  <w:style w:type="paragraph" w:styleId="FactTitle">
    <w:name w:val="Fact Title"/>
    <w:pPr>
      <w:spacing w:before="240"/>
    </w:pPr>
    <w:rPr><w:b/><w:u w:val="single"/></w:rPr>
  </w:style>

  <w:style w:type="paragraph" w:styleId="DeclarationPara">
    <w:name w:val="Declaration Paragraph"/>
    <w:pPr>
      <w:spacing w:after="240" w:line="{LINE_SPACING}" w:lineRule="auto"/>
      <w:ind w:firstLine="720"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="{FONT}" w:hAnsi="{FONT}"/>
      <w:sz w:val="28"/><w:szCs w:val="28"/>
    </w:rPr>
  </w:style>

  <w:style w:type="paragraph" w:styleId="NumberedFact">
    <w:name w:val="Numbered Fact"/>
    <w:pPr>
      <w:spacing w:after="240" w:line="{LINE_SPACING}" w:lineRule="auto"/>
      <w:ind w:left="720" w:hanging="720"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="{FONT}" w:hAnsi="{FONT}"/>
      <w:sz w:val="28"/><w:szCs w:val="28"/>
    </w:rPr>
  </w:style>
</w:styles>'''

CONTENT_TYPES_XML = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
  <Default Extension="xml" ContentType="application/xml"/>
  <Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>
  <Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/>
</Types>'''

RELS_XML = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/>
</Relationships>'''

DOCUMENT_RELS_XML = '''<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>
</Relationships>'''


# ============================================================================
# COVER PAGE TEMPLATE (Ninth Circuit Style)
# ============================================================================

COVER_NINTH_XML = '''    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:t>Case No. {CASE_NUMBER}</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="240"/></w:pPr>
      <w:r><w:rPr><w:b/></w:rPr><w:t>IN THE UNITED STATES COURT OF APPEALS</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:rPr><w:b/></w:rPr><w:t>FOR THE {CIRCUIT} CIRCUIT</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
      <w:r><w:t>{APPELLANT},</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:rPr><w:i/></w:rPr><w:t>Plaintiff-Appellant,</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="240"/></w:pPr>
      <w:r><w:t>v.</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="240"/></w:pPr>
      <w:r><w:t>{APPELLEE},</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:rPr><w:i/></w:rPr><w:t>Defendants-Appellees.</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
      <w:r><w:rPr><w:b/></w:rPr><w:t>{FILING_NAME}</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/><w:spacing w:before="480"/></w:pPr>
      <w:r><w:t>Appeal from the United States District Court</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:t>for the District of Oregon</w:t></w:r>
    </w:p>
    <w:p>
      <w:pPr><w:jc w:val="center"/></w:pPr>
      <w:r><w:t>{JUDGE_NAME}, District Judge</w:t></w:r>
    </w:p>
    <w:p>
      <w:r><w:br w:type="page"/></w:r>
    </w:p>
'''


# ============================================================================
# DECLARATION BUILDER CLASS
# ============================================================================

class DeclarationBuilder:
    """
    Builds declarations using pure Python XML manipulation.
    No subprocess calls - uses zipfile directly.
    """
    
    def __init__(
        self,
        jurisdiction: str = "ninth",
        case_number: str = "",
        declarant: str = "",
        appellant: str = "",
        appellee: str = "",
        judge_name: str = "",
    ):
        self.config = JURISDICTIONS.get(jurisdiction, JURISDICTIONS["ninth"])
        self.case_number = case_number
        self.declarant = declarant
        self.appellant = appellant or declarant
        self.appellee = appellee or "DEFENDANTS"
        self.judge_name = judge_name
        self.facts: List[DeclarationFact] = []
        self.execution_date = datetime.now().strftime("%B %d, %Y")
        self.execution_location = ""
    
    def add_fact(
        self,
        title: str,
        narrative: str = "",
        time_place: str = "",
        parties: str = "",
        opposing_link: str = "",
        defendant: str = "Defendants",
        witnesses: Optional[List[str]] = None,
        evidence_uids: Optional[List[str]] = None,
    ) -> None:
        """Add a fact with 2+2+1 structure."""
        
        # Auto-generate structure from narrative if not provided
        circ_time = time_place or f"On the date in question, at the location described herein"
        circ_parties = parties or f"At said time and location, {defendant} were present"
        elem_primary = narrative[:500] if narrative else "[PRIMARY ELEMENT DESCRIPTION]"
        elem_supporting = "[SUPPORTING ELEMENT DESCRIPTION]"
        link = opposing_link or f"{defendant} caused or participated in these events"
        
        fact = DeclarationFact(
            title=title.upper(),
            circumstance_time_place=circ_time,
            circumstance_parties=circ_parties,
            element_primary=elem_primary,
            element_supporting=elem_supporting,
            party_link=link,
            defendant=defendant,
            witnesses=witnesses or [],
            evidence_uids=evidence_uids or [],
        )
        self.facts.append(fact)
    
    def _build_paragraph(
        self,
        text: str,
        style: Optional[str] = None,
        bold: bool = False,
        italic: bool = False,
        center: bool = False,
        indent_first: bool = False,
        spacing_before: int = 0,
    ) -> str:
        """Build a paragraph XML element."""
        
        pPr_parts = []
        if style:
            pPr_parts.append(f'<w:pStyle w:val="{style}"/>')
        if center:
            pPr_parts.append('<w:jc w:val="center"/>')
        if indent_first:
            pPr_parts.append('<w:ind w:firstLine="720"/>')
        if spacing_before:
            pPr_parts.append(f'<w:spacing w:before="{spacing_before}"/>')
        
        pPr = f"<w:pPr>{' '.join(pPr_parts)}</w:pPr>" if pPr_parts else ""
        
        rPr_parts = []
        if bold:
            rPr_parts.append('<w:b/>')
        if italic:
            rPr_parts.append('<w:i/>')
        
        rPr = f"<w:rPr>{' '.join(rPr_parts)}</w:rPr>" if rPr_parts else ""
        
        # Escape XML special characters
        safe_text = xml_escape(text)
        
        return f'''    <w:p>
      {pPr}
      <w:r>
        {rPr}
        <w:t>{safe_text}</w:t>
      </w:r>
    </w:p>'''
    
    def _build_fact_block(self, fact: DeclarationFact, num: int) -> str:
        """Build XML for a single fact with 2+2+1 structure."""
        
        lines = []
        
        # Fact title
        lines.append(self._build_paragraph(
            f"FACT {num}: {fact.title}",
            bold=True,
            spacing_before=360
        ))
        
        # Circumstance 1: Time/Place
        lines.append(self._build_paragraph(
            f"CIRCUMSTANCE 1: {fact.circumstance_time_place}",
            indent_first=True,
            spacing_before=120
        ))
        
        # Circumstance 2: Parties
        lines.append(self._build_paragraph(
            f"CIRCUMSTANCE 2: {fact.circumstance_parties}",
            indent_first=True
        ))
        
        # Element 1: Primary
        lines.append(self._build_paragraph(
            f"ELEMENT 1: {fact.element_primary}",
            indent_first=True,
            spacing_before=120
        ))
        
        # Element 2: Supporting
        lines.append(self._build_paragraph(
            f"ELEMENT 2: {fact.element_supporting}",
            indent_first=True
        ))
        
        # Party Link
        lines.append(self._build_paragraph(
            f"PARTY LINK ({fact.defendant}): {fact.party_link}",
            indent_first=True,
            spacing_before=120
        ))
        
        # Witnesses (if any)
        if fact.witnesses:
            witnesses_str = ", ".join(fact.witnesses)
            lines.append(self._build_paragraph(
                f"WITNESSES: {witnesses_str}",
                indent_first=True,
                italic=True
            ))
        
        # Evidence UIDs (if any)
        if fact.evidence_uids:
            uids_str = ", ".join(fact.evidence_uids)
            lines.append(self._build_paragraph(
                f"EVIDENCE: [{uids_str}]",
                indent_first=True,
                italic=True
            ))
        
        return "\n".join(lines)
    
    def _build_cover(self, filing_name: str) -> str:
        """Build cover page XML with placeholders resolved."""
        
        cover = COVER_NINTH_XML
        cover = cover.replace("{CASE_NUMBER}", self.case_number)
        cover = cover.replace("{CIRCUIT}", self.config.circuit)
        cover = cover.replace("{APPELLANT}", self.appellant.upper())
        cover = cover.replace("{APPELLEE}", self.appellee.upper())
        cover = cover.replace("{FILING_NAME}", filing_name.upper())
        cover = cover.replace("{JUDGE_NAME}", self.judge_name)
        
        return cover
    
    def _build_declaration_header(self) -> str:
        """Build declaration header."""
        
        lines = []
        
        # Title
        lines.append(self._build_paragraph(
            f"DECLARATION OF {self.declarant.upper()}",
            bold=True,
            center=True,
            spacing_before=240
        ))
        
        # Preamble
        preamble = (
            f"I, {self.declarant}, declare under penalty of perjury under the laws of "
            f"the United States and the State of Oregon that the following is true and correct:"
        )
        lines.append(self._build_paragraph(
            preamble,
            indent_first=True,
            spacing_before=240
        ))
        
        return "\n".join(lines)
    
    def _build_signature_block(self) -> str:
        """Build signature block."""
        
        lines = []
        
        # Closing statement
        lines.append(self._build_paragraph(
            "I declare under penalty of perjury that the foregoing is true and correct.",
            indent_first=True,
            spacing_before=480
        ))
        
        # Execution line
        exec_line = f"Executed on {self.execution_date}"
        if self.execution_location:
            exec_line += f" at {self.execution_location}"
        exec_line += "."
        
        lines.append(self._build_paragraph(
            exec_line,
            indent_first=True,
            spacing_before=240
        ))
        
        # Signature line
        lines.append(self._build_paragraph(
            "_______________________________",
            spacing_before=720
        ))
        
        # Name
        lines.append(self._build_paragraph(self.declarant))
        
        return "\n".join(lines)
    
    def build(self, filing_name: str = "DECLARATION", include_cover: bool = True) -> bytes:
        """
        Build the complete document and return as bytes.
        
        Returns .docx file contents as bytes (ready to write to file).
        """
        
        content_parts = []
        
        # Cover page (optional)
        if include_cover:
            content_parts.append(self._build_cover(filing_name))
        
        # Declaration header
        content_parts.append(self._build_declaration_header())
        
        # All facts
        for i, fact in enumerate(self.facts, 1):
            content_parts.append(self._build_fact_block(fact, i))
        
        # Signature block
        content_parts.append(self._build_signature_block())
        
        # Combine all content
        content = "\n".join(content_parts)
        
        # Build document.xml
        document_xml = DOCUMENT_XML_TEMPLATE.format(
            CONTENT=content,
            MARGIN_TOP=self.config.margins["top"],
            MARGIN_RIGHT=self.config.margins["right"],
            MARGIN_BOTTOM=self.config.margins["bottom"],
            MARGIN_LEFT=self.config.margins["left"],
        )
        
        # Build styles.xml
        styles_xml = STYLES_XML.format(
            FONT=self.config.font_name,
            FONT_SIZE=self.config.font_size,
            LINE_SPACING=self.config.line_spacing,
        )
        
        # Create .docx in memory using zipfile
        docx_buffer = io.BytesIO()
        
        with zipfile.ZipFile(docx_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
            zf.writestr('[Content_Types].xml', CONTENT_TYPES_XML)
            zf.writestr('_rels/.rels', RELS_XML)
            zf.writestr('word/_rels/document.xml.rels', DOCUMENT_RELS_XML)
            zf.writestr('word/document.xml', document_xml)
            zf.writestr('word/styles.xml', styles_xml)
        
        return docx_buffer.getvalue()
    
    def save(self, path: str, filing_name: str = "DECLARATION", include_cover: bool = True) -> str:
        """Build and save the document to a file."""
        
        docx_bytes = self.build(filing_name, include_cover)
        
        with open(path, 'wb') as f:
            f.write(docx_bytes)
        
        return path


# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def create_declaration(
    declarant: str,
    case_number: str,
    facts: List[Dict[str, Any]],
    jurisdiction: str = "ninth",
    output_path: Optional[str] = None,
) -> bytes:
    """
    Convenience function to create a declaration.
    
    Args:
        declarant: Name of person making declaration
        case_number: Case number
        facts: List of fact dicts with keys: title, narrative, time_place, parties, opposing_link
        jurisdiction: Circuit (default: ninth)
        output_path: Optional path to save file
        
    Returns:
        bytes: The .docx file contents
    """
    
    builder = DeclarationBuilder(
        jurisdiction=jurisdiction,
        case_number=case_number,
        declarant=declarant,
    )
    
    for fact in facts:
        builder.add_fact(**fact)
    
    docx_bytes = builder.build()
    
    if output_path:
        with open(output_path, 'wb') as f:
            f.write(docx_bytes)
    
    return docx_bytes


# ============================================================================
# DEMO
# ============================================================================

if __name__ == "__main__":
    # Demo: Tyler's declaration about defendants' false statements
    
    builder = DeclarationBuilder(
        jurisdiction="ninth",
        case_number="25-6461",
        declarant="Tyler Lofall",
        appellant="Tyler Lofall",
        appellee="Clackamas County, et al.",
        judge_name="Hon. Susan Brnovich",
    )
    
    builder.execution_location = "Oregon City, Oregon"
    
    # Fact 1: False statements in Motion to Dismiss
    builder.add_fact(
        title="False Statements in Motion to Dismiss",
        time_place="In December 2024, Defendants filed a Motion to Dismiss in this matter",
        parties="Defendants, through their counsel, prepared and submitted the Motion to Dismiss",
        opposing_link="Clackamas County deliberately included material misrepresentations in their Motion to Dismiss with intent to deceive this Court",
        defendant="Clackamas County",
        evidence_uids=["F01A", "F01B"],
    )
    
    # Fact 2: Repeated false statements in late Reply
    builder.add_fact(
        title="Repeated False Statements in Late-Filed Reply",
        time_place="Defendants subsequently filed a Reply Brief after the deadline",
        parties="Defendants' counsel filed the untimely Reply containing the same false statements",
        opposing_link="Clackamas County compounded their fraud by repeating identical false statements in a procedurally improper late filing",
        defendant="Clackamas County",
        evidence_uids=["F02A"],
    )
    
    # Fact 3: Pattern of fraud
    builder.add_fact(
        title="Pattern Constituting Fraud Upon the Court",
        time_place="Throughout these proceedings, Defendants have engaged in systematic misrepresentation",
        parties="All Defendants, through counsel, have participated in this pattern of deception",
        opposing_link="The cumulative conduct of Clackamas County and its agents constitutes fraud upon this Court warranting sanctions and adverse inference",
        defendant="Clackamas County et al.",
        evidence_uids=["F03A", "F03B", "F03C"],
    )
    
    # Build and save
    output_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
        
    output_path = os.path.join(output_dir, "DECLARATION_FALSE_STATEMENTS_v2.docx")
    builder.save(output_path, filing_name="DECLARATION IN SUPPORT OF REQUEST FOR JUDICIAL NOTICE")
    
    print(f"[+] Created: {output_path}")
    print(f"  Declarant: {builder.declarant}")
    print(f"  Case: {builder.case_number}")
    print(f"  Facts: {len(builder.facts)}")
    print(f"  Circuit: {builder.config.circuit}")
