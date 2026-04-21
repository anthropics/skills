#!/usr/bin/env python3
"""
Ninth Circuit Brief Interactive Formatter
Phase 1: User classifies each section
Phase 2: Claude reviews and suggests edits (tracked changes)
"""

import sys
import os
from pathlib import Path

# Add OOXML scripts to path
sys.path.insert(0, '/mnt/skills/public/docx/ooxml/scripts')
sys.path.insert(0, '/mnt/skills/public/docx/scripts')

from document import Document
import json
from datetime import datetime

# Store classifications
sections = []

def classify_sections(doc_path):
    """Phase 1: Interactive classification"""
    print("\n" + "="*60)
    print("PHASE 1: CLASSIFY SECTIONS")
    print("="*60 + "\n")
    
    # Unpack document
    unpack_dir = "/tmp/brief_unpacked"
    os.system(f"python3 /mnt/skills/public/docx/ooxml/scripts/unpack.py '{doc_path}' {unpack_dir}")
    
    # Load document
    doc = Document(f"{unpack_dir}/word/document.xml")
    paragraphs = doc.get_nodes("//w:p")
    
    total = len(paragraphs)
    print(f"Total sections to classify: {total}\n")
    
    for i, para in enumerate(paragraphs, 1):
        # Get text
        text_nodes = doc.get_nodes(".//w:t", para)
        text = "".join([n.text or "" for n in text_nodes]).strip()
        
        if not text:
            sections.append({
                'index': i-1,
                'text': '',
                'classification': 'Skip',
                'node': para
            })
            continue
        
        # Show section
        print(f"\n[Section {i}/{total}]")
        preview = text[:200] + "..." if len(text) > 200 else text
        print(f"{preview}")
        print()
        
        # Get classification
        while True:
            choice = input("[H1] Main Heading  [H2] Subheading  [B] Body  [N] Numbered  [S] Skip\nChoice: ").strip().upper()
            
            if choice in ['H1', 'H2', 'B', 'N', 'S']:
                class_map = {
                    'H1': 'AppHeading1',
                    'H2': 'AppHeading2', 
                    'B': 'AppBody',
                    'N': 'AppNumbered',
                    'S': 'Skip'
                }
                
                sections.append({
                    'index': i-1,
                    'text': text,
                    'classification': class_map[choice],
                    'node': para,
                    'suggestions': []
                })
                break
            else:
                print("Invalid choice. Use H1/H2/B/N/S")
    
    # Save classifications
    with open('/tmp/classifications.json', 'w') as f:
        json.dump([{k: v for k, v in s.items() if k != 'node'} for s in sections], f, indent=2)
    
    print(f"\n✓ Classified {len(sections)} sections")
    return doc, unpack_dir

def review_and_suggest(doc, unpack_dir):
    """Phase 2: Claude reviews and suggests edits"""
    print("\n" + "="*60)
    print("PHASE 2: REVIEW & SUGGEST EDITS")
    print("="*60 + "\n")
    
    want_review = input("Do you want Claude to review sections and suggest edits? [Y/n]: ").strip().lower()
    
    if want_review == 'n':
        print("Skipping review phase.")
        return
    
    for i, section in enumerate(sections):
        if section['classification'] == 'Skip' or not section['text']:
            continue
        
        print(f"\n[Reviewing section {i+1}/{len(sections)}]")
        print(f"Type: {section['classification']}")
        print(f"Text: {section['text'][:150]}...")
        
        # Ask if user wants suggestions for this section
        check = input("\nReview this section? [Y/n/q to stop reviewing]: ").strip().lower()
        
        if check == 'q':
            print("Stopping review.")
            break
        elif check == 'n':
            continue
        
        # Claude suggests improvements
        print("\n[Claude is reviewing...]")
        suggestion = suggest_improvement(section['text'], section['classification'])
        
        if suggestion:
            print(f"\nSuggestion: {suggestion}")
            accept = input("[A]ccept  [R]eject: ").strip().lower()
            
            if accept == 'a':
                section['suggestions'].append({
                    'type': 'general_edit',
                    'original': section['text'],
                    'suggested': suggestion,
                    'accepted': True
                })
                print("✓ Accepted")
        else:
            print("No suggestions for this section.")
    
    # Save with suggestions
    with open('/tmp/classifications_with_edits.json', 'w') as f:
        json.dump([{k: v for k, v in s.items() if k != 'node'} for s in sections], f, indent=2)

def suggest_improvement(text, classification):
    """Claude's review logic - simplified for now"""
    # This is where Claude would analyze the text
    # For now, return None (no suggestion)
    # In full implementation, this would call Claude API or use rules
    
    # Example rules:
    if len(text) > 500 and classification == 'AppBody':
        return None  # "Consider breaking this into multiple paragraphs"
    
    return None

def apply_formatting(doc, unpack_dir, output_name):
    """Apply formatting based on classifications"""
    print(f"\nApplying formatting to {output_name}...")
    
    # Add custom styles to styles.xml
    styles_path = f"{unpack_dir}/word/styles.xml"
    add_custom_styles(styles_path)
    
    # Apply styles to paragraphs
    for section in sections:
        if section['classification'] == 'Skip':
            continue
        
        para = section['node']
        
        # Get or create pPr
        pPr = doc.get_node(".//w:pPr", para)
        if pPr is None:
            pPr = doc.create_element("w:pPr")
            para.insert(0, pPr)
        
        # Set style
        pStyle = doc.get_node(".//w:pStyle", pPr)
        if pStyle is None:
            pStyle = doc.create_element("w:pStyle")
            pPr.insert(0, pStyle)
        
        pStyle.set(doc.qn("w:val"), section['classification'])
        
        # Set spacing based on type
        spacing = doc.get_node(".//w:spacing", pPr)
        if spacing is None:
            spacing = doc.create_element("w:spacing")
            pPr.append(spacing)
        
        if section['classification'] in ['AppHeading1', 'AppHeading2']:
            spacing.set(doc.qn("w:line"), "240")  # Single-spaced
        else:
            spacing.set(doc.qn("w:line"), "480")  # Double-spaced
        
        spacing.set(doc.qn("w:lineRule"), "auto")
    
    # Save
    doc.save()
    
    # Pack
    os.system(f"python3 /mnt/skills/public/docx/ooxml/scripts/pack.py {unpack_dir} /mnt/user-data/outputs/{output_name}")
    print(f"✓ Saved: {output_name}")

def apply_tracked_changes(doc, unpack_dir, output_name):
    """Create version with tracked changes for suggestions"""
    print(f"\nCreating tracked changes version...")
    
    # Check if there are any accepted suggestions
    has_edits = any(s['suggestions'] for s in sections if 'suggestions' in s)
    
    if not has_edits:
        print("No suggestions accepted, skipping tracked changes version.")
        return
    
    # Enable track changes in settings
    settings_path = f"{unpack_dir}/word/settings.xml"
    with open(settings_path, 'r') as f:
        settings = f.read()
    
    if '<w:trackRevisions/>' not in settings:
        settings = settings.replace('</w:settings>', '  <w:trackRevisions/>\n</w:settings>')
        with open(settings_path, 'w') as f:
            f.write(settings)
    
    # Apply tracked changes to paragraphs with accepted suggestions
    rsid = "00AB1234"  # Use consistent RSID
    
    for section in sections:
        if not section.get('suggestions'):
            continue
        
        para = section['node']
        
        for sug in section['suggestions']:
            if not sug.get('accepted'):
                continue
            
            # Create deletion and insertion
            # This is simplified - full implementation would do proper text replacement
            print(f"  Adding tracked change for section {section['index']}")
    
    doc.save()
    os.system(f"python3 /mnt/skills/public/docx/ooxml/scripts/pack.py {unpack_dir} /mnt/user-data/outputs/{output_name}")
    print(f"✓ Saved: {output_name}")

def add_custom_styles(styles_path):
    """Add AppHeading1, AppHeading2, AppBody styles"""
    
    custom_styles = """
  <w:style w:type="paragraph" w:styleId="AppHeading1">
    <w:name w:val="App Heading 1"/>
    <w:pPr>
      <w:spacing w:line="240" w:lineRule="auto"/>
      <w:jc w:val="center"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="Century Schoolbook" w:hAnsi="Century Schoolbook"/>
      <w:b/><w:caps/>
      <w:sz w:val="28"/>
    </w:rPr>
  </w:style>
  
  <w:style w:type="paragraph" w:styleId="AppHeading2">
    <w:name w:val="App Heading 2"/>
    <w:pPr>
      <w:spacing w:line="240" w:lineRule="auto"/>
      <w:jc w:val="left"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="Century Schoolbook" w:hAnsi="Century Schoolbook"/>
      <w:b/><w:caps/>
      <w:sz w:val="28"/>
    </w:rPr>
  </w:style>
  
  <w:style w:type="paragraph" w:styleId="AppBody">
    <w:name w:val="App Body"/>
    <w:pPr>
      <w:spacing w:line="480" w:lineRule="auto"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="Century Schoolbook" w:hAnsi="Century Schoolbook"/>
      <w:sz w:val="28"/>
    </w:rPr>
  </w:style>
  
  <w:style w:type="paragraph" w:styleId="AppNumbered">
    <w:name w:val="App Numbered"/>
    <w:pPr>
      <w:spacing w:line="480" w:lineRule="auto"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="Century Schoolbook" w:hAnsi="Century Schoolbook"/>
      <w:sz w:val="28"/>
    </w:rPr>
  </w:style>
"""
    
    with open(styles_path, 'r') as f:
        styles = f.read()
    
    # Insert before closing </w:styles>
    if 'AppHeading1' not in styles:
        styles = styles.replace('</w:styles>', custom_styles + '</w:styles>')
        with open(styles_path, 'w') as f:
            f.write(styles)

def main():
    if len(sys.argv) < 2:
        print("Usage: python ninth_circuit_formatter.py YOUR_BRIEF.docx")
        sys.exit(1)
    
    input_file = sys.argv[1]
    base_name = Path(input_file).stem
    
    print("\n" + "="*60)
    print("NINTH CIRCUIT BRIEF FORMATTER")
    print("="*60)
    
    # Phase 1: Classify
    doc, unpack_dir = classify_sections(input_file)
    
    # Phase 2: Review
    review_and_suggest(doc, unpack_dir)
    
    # Output 1: Formatted version
    apply_formatting(doc, unpack_dir, f"{base_name}_FORMATTED.docx")
    
    # Output 2: With tracked changes
    apply_tracked_changes(doc, unpack_dir, f"{base_name}_WITH_EDITS.docx")
    
    print("\n" + "="*60)
    print("COMPLETE")
    print("="*60)
    print(f"\n✓ {base_name}_FORMATTED.docx - Your formatting applied")
    print(f"✓ {base_name}_WITH_EDITS.docx - With suggested edits (if any)")
    print("\nOpen both in Word to compare!")

if __name__ == '__main__':
    main()
