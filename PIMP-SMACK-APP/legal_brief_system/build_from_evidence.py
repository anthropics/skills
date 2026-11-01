#!/usr/bin/env python3
"""
Brief Builder - Assembles brief from evidence pool with linked footnotes
Keeps facts grouped with their references and generates proper footnotes

*** CRITICAL: NO REWORDING ***
This script outputs EXACT text from your data files.
It does NOT paraphrase, summarize, or modify your words.
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime

# Import exact quote loader
try:
    from exact_quote_loader import ExactQuoteLoader
except ImportError:
    ExactQuoteLoader = None


class FootnoteManager:
    """Manage footnotes and cross-references"""
    
    def __init__(self):
        self.footnotes: List[Dict] = []
        self.footnote_counter = 0
    
    def add_footnote(self, text: str, source_fact_id: str = None) -> int:
        """Add a footnote and return its number"""
        self.footnote_counter += 1
        self.footnotes.append({
            'number': self.footnote_counter,
            'text': text,
            'source': source_fact_id
        })
        return self.footnote_counter
    
    def get_footnote_xml(self) -> str:
        """Generate XML for all footnotes"""
        xml_parts = []
        for fn in self.footnotes:
            xml_parts.append(f'''<w:footnote w:id="{fn['number']}">
                <w:p>
                    <w:r>
                        <w:rPr><w:vertAlign w:val="superscript"/></w:rPr>
                        <w:t>{fn['number']}</w:t>
                    </w:r>
                    <w:r>
                        <w:t xml:space="preserve"> {self._escape_xml(fn['text'])}</w:t>
                    </w:r>
                </w:p>
            </w:footnote>''')
        return '\n'.join(xml_parts)
    
    def _escape_xml(self, text: str) -> str:
        return (text.replace('&', '&amp;')
                    .replace('<', '&lt;')
                    .replace('>', '&gt;'))


class EvidencePoolProcessor:
    """Process evidence pool to build brief sections"""
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
        self.evidence_pool = self._load_json('evidence_pool.json')
        self.authorities = self._load_json('authorities.json')
        self.footnotes = FootnoteManager()
        
        # Index facts by ID and category
        self.facts_by_id = {f['id']: f for f in self.evidence_pool.get('facts', [])}
        self.facts_by_category = {}
        for fact in self.evidence_pool.get('facts', []):
            cat = fact.get('category', 'other')
            if cat not in self.facts_by_category:
                self.facts_by_category[cat] = []
            self.facts_by_category[cat].append(fact)
        
        # Index evidence by ID
        self.evidence_by_id = {e['id']: e for e in self.evidence_pool.get('evidence', [])}
    
    def _load_json(self, filename: str) -> Dict:
        path = self.data_dir / filename
        if path.exists():
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}
    
    def get_fact_with_cite(self, fact_id: str, include_footnote: bool = True) -> str:
        """Get a fact statement with its citation and optional footnote"""
        fact = self.facts_by_id.get(fact_id)
        if not fact:
            return f"[FACT NOT FOUND: {fact_id}]"
        
        statement = fact['statement']
        cite = fact.get('record_cite', '')
        
        # Build the text with citation
        text = statement
        if cite:
            text += f" ({cite}.)"
        
        # Add footnote if there's additional context
        if include_footnote and fact.get('footnote_text'):
            fn_num = self.footnotes.add_footnote(
                fact['footnote_text'],
                fact_id
            )
            text += f"[fn:{fn_num}]"
        
        return text
    
    def get_facts_for_section(self, section_name: str) -> List[Dict]:
        """Get all facts that should appear in a section"""
        facts = []
        for fact in self.evidence_pool.get('facts', []):
            if section_name in fact.get('used_in_sections', []):
                facts.append(fact)
        return sorted(facts, key=lambda x: x.get('date', ''))
    
    def get_facts_by_category(self, category: str) -> List[Dict]:
        """Get all facts in a category"""
        return self.facts_by_category.get(category, [])
    
    def build_statement_of_case(self) -> str:
        """Build Statement of Case from evidence pool"""
        facts = self.get_facts_for_section('statement_of_case')
        
        paragraphs = []
        for fact in facts:
            text = self.get_fact_with_cite(fact['id'], include_footnote=True)
            
            # Add cross-reference footnotes
            cross_refs = fact.get('cross_references', [])
            if cross_refs:
                ref_texts = []
                for ref_id in cross_refs:
                    ref_fact = self.facts_by_id.get(ref_id)
                    if ref_fact:
                        ref_texts.append(f"See also {ref_fact['statement'][:50]}... ({ref_fact.get('record_cite', '')})")
                if ref_texts:
                    fn_num = self.footnotes.add_footnote(
                        " ".join(ref_texts),
                        fact['id']
                    )
                    text += f"[fn:{fn_num}]"
            
            paragraphs.append(text)
        
        return paragraphs
    
    def build_argument_section(self, argument_id: str) -> str:
        """Build argument section from evidence pool"""
        facts = self.get_facts_for_section(argument_id)
        
        paragraphs = []
        for fact in facts:
            # Get the fact with legal significance
            text = self.get_fact_with_cite(fact['id'])
            
            # Add legal significance as context
            if fact.get('legal_significance'):
                text += f" This constitutes a {fact['legal_significance']}."
            
            paragraphs.append(text)
        
        return paragraphs
    
    def get_linked_evidence_chain(self, fact_id: str) -> List[Dict]:
        """Get a fact and all its cross-referenced facts as a chain"""
        chain = []
        visited = set()
        
        def traverse(fid):
            if fid in visited:
                return
            visited.add(fid)
            fact = self.facts_by_id.get(fid)
            if fact:
                chain.append(fact)
                for ref in fact.get('cross_references', []):
                    traverse(ref)
        
        traverse(fact_id)
        return chain


class BriefBuilder:
    """Build complete brief from evidence pool"""
    
    def __init__(self, data_dir: str):
        self.data_dir = Path(data_dir)
        self.processor = EvidencePoolProcessor(data_dir)
        self.case_info = self._load_json('case_info.json')
        self.arguments = self._load_json('arguments.json')
        self.issues = self._load_json('issues_presented.json')
    
    def _load_json(self, filename: str) -> Dict:
        path = self.data_dir / filename
        if path.exists():
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}
    
    def build_complete_brief(self) -> Dict:
        """Build all sections of the brief"""
        
        print("\n" + "="*60)
        print("BUILDING BRIEF FROM EVIDENCE POOL")
        print("="*60)
        
        sections = {}
        
        # Statement of Case
        print("\n--- Building Statement of Case ---")
        sections['statement_of_case'] = {
            'paragraphs': self.processor.build_statement_of_case(),
            'footnotes': self.processor.footnotes.footnotes.copy()
        }
        print(f"  Generated {len(sections['statement_of_case']['paragraphs'])} paragraphs")
        print(f"  Created {len(sections['statement_of_case']['footnotes'])} footnotes")
        
        # Arguments
        print("\n--- Building Arguments ---")
        for arg in self.arguments.get('arguments', []):
            arg_id = f"argument_{arg['number']}"
            sections[arg_id] = {
                'heading': arg['heading'],
                'paragraphs': self.processor.build_argument_section(arg_id),
            }
            
            for sub in arg.get('subarguments', []):
                sub_id = f"argument_{arg['number']}_{sub['letter']}"
                sections[sub_id] = {
                    'heading': sub['heading'],
                    'paragraphs': self.processor.build_argument_section(sub_id),
                }
        
        # Summary
        sections['summary'] = self._build_summary(sections)
        
        print(f"\n✓ Built {len(sections)} sections")
        
        return sections
    
    def _build_summary(self, sections: Dict) -> Dict:
        """Build summary of argument from argument sections"""
        summary_parts = []
        
        for arg in self.arguments.get('arguments', []):
            arg_id = f"argument_{arg['number']}"
            section = sections.get(arg_id, {})
            
            # Create summary entry
            summary_parts.append({
                'number': arg['number'],
                'heading': arg['heading'],
                'summary': f"[Summarize argument {arg['number']} here]"
            })
        
        return {'parts': summary_parts}
    
    def export_for_review(self, output_path: Path = None) -> str:
        """Export built brief as readable text for review"""
        
        sections = self.build_complete_brief()
        
        output = []
        output.append("="*70)
        output.append("BRIEF CONTENT - REVIEW DRAFT")
        output.append("="*70)
        output.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        output.append("")
        
        # Statement of Case
        output.append("\n" + "="*50)
        output.append("STATEMENT OF THE CASE")
        output.append("="*50 + "\n")
        
        soc = sections.get('statement_of_case', {})
        for i, para in enumerate(soc.get('paragraphs', []), 1):
            output.append(f"{i}. {para}")
            output.append("")
        
        # Footnotes for Statement of Case
        if soc.get('footnotes'):
            output.append("\n--- Footnotes ---")
            for fn in soc['footnotes']:
                output.append(f"[{fn['number']}] {fn['text']}")
            output.append("")
        
        # Arguments
        for arg in self.arguments.get('arguments', []):
            output.append("\n" + "="*50)
            output.append(f"{arg['number']}. {arg['heading']}")
            output.append("="*50 + "\n")
            
            arg_id = f"argument_{arg['number']}"
            arg_section = sections.get(arg_id, {})
            
            for para in arg_section.get('paragraphs', []):
                output.append(para)
                output.append("")
            
            # Subarguments
            for sub in arg.get('subarguments', []):
                output.append(f"\n    {sub['letter']}. {sub['heading']}")
                output.append("    " + "-"*40)
                
                sub_id = f"argument_{arg['number']}_{sub['letter']}"
                sub_section = sections.get(sub_id, {})
                
                for para in sub_section.get('paragraphs', []):
                    output.append(f"    {para}")
                    output.append("")
        
        text = '\n'.join(output)
        
        # Save if output path provided
        if output_path:
            output_path = Path(output_path)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(text)
            print(f"\n✓ Exported to: {output_path}")
        
        return text


def main():
    """Build brief and export for review"""
    
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"
    output_dir = script_dir / "output"
    
    builder = BriefBuilder(str(data_dir))
    
    # Export readable version for review
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = output_dir / f"BRIEF_REVIEW_{timestamp}.txt"
    
    builder.export_for_review(output_path)
    
    print("\n" + "="*60)
    print("DONE!")
    print("="*60)
    print(f"\nReview file: {output_path}")
    print("\nThis file shows how the evidence pool facts flow into")
    print("the brief sections, with footnotes for cross-references.")


if __name__ == "__main__":
    main()
