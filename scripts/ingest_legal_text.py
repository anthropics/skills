import json
import re
import argparse
from pathlib import Path
from collections import Counter

def detect_header_footer_patterns(text_blocks):
    """
    Detects repeating patterns that look like headers or footers.
    Logic:
    - Look for short lines (under 100 chars) that repeat exactly or with slight variation (like page numbers).
    - Look for lines containing "Case No." or "Page" that appear regularly.
    """
    # Simple frequency analysis for exact matches
    line_counts = Counter(text_blocks)
    repeating_lines = {line for line, count in line_counts.items() if count > 1}
    
    # Filter for likely headers/footers
    header_footer_candidates = set()
    for line in repeating_lines:
        # If it's a case number
        if re.search(r'\d{2}-\d{4}', line):
            header_footer_candidates.add(line)
        # If it's a page number pattern (e.g., "Page 1 of 10", "- 1 -")
        elif re.search(r'Page \d+|-\s*\d+\s*-', line):
            header_footer_candidates.add(line)
        # If it's very short and repeats often (e.g. "Opening Brief")
        elif len(line) < 50 and line_counts[line] > 2:
            header_footer_candidates.add(line)
            
    return header_footer_candidates

def identify_style(text):
    """
    Guess the style of a text block based on its content.
    """
    text = text.strip()
    
    # Heading 1: All Caps, short-ish
    if text.isupper() and len(text) < 100 and not text.startswith("NO."):
        return "HEADING_1"
    
    # Heading 2: Roman Numerals (I., II., III.)
    if re.match(r'^[IVX]+\.\s+', text):
        return "HEADING_2"
        
    # Heading 3: Letters (A., B., C.)
    if re.match(r'^[A-Z]\.\s+', text):
        return "HEADING_3"
        
    # Heading 4: Numbers (1., 2., 3.)
    if re.match(r'^\d+\.\s+', text):
        return "HEADING_4"
        
    # Quoted Citation (starts with quote or block indent pattern - hard to detect in raw text without context)
    if text.startswith('"') or text.startswith('“'):
        return "QUOTED_CITATION"
        
    return "NORMAL"

def parse_text_to_layout(raw_text):
    """
    Parses raw text into the JSON layout structure.
    """
    # Split by double newlines to find paragraphs
    blocks = [b.strip() for b in raw_text.split('\n\n') if b.strip()]
    
    # Detect headers/footers to exclude
    ignore_set = detect_header_footer_patterns(blocks)
    
    layout = []
    
    for block in blocks:
        # Skip if it's a detected header/footer
        if block in ignore_set:
            continue
            
        # Skip page numbers if they weren't caught by exact match (e.g. "1", "2")
        if re.match(r'^\d+$', block) or re.match(r^'-\s*\d+\s*-$', block):
            continue

        style = identify_style(block)
        
        layout.append({
            "type": "paragraph",
            "style": style,
            "text": block
        })
        
        # Add spacer after headings for visual separation in JSON (optional, builder handles spacing)
        # But user wants "tight" script, so maybe minimal is better.
        
    return layout

def main():
    parser = argparse.ArgumentParser(description="Ingest raw text and convert to Ninth Circuit JSON config.")
    parser.add_argument("input_file", help="Path to the text file to ingest.")
    parser.add_argument("--output", default="ingested_config.json", help="Output JSON file path.")
    args = parser.parse_args()
    
    input_path = Path(args.input_file)
    if not input_path.exists():
        print(f"Error: File {input_path} not found.")
        return

    with open(input_path, 'r', encoding='utf-8') as f:
        raw_text = f.read()
        
    layout = parse_text_to_layout(raw_text)
    
    # Create the full config structure
    config = {
        "$schema": "./filing_config.schema.json",
        "metadata": {
            "tool_name": "TextIngestor",
            "output_filename": f"Ingested_{input_path.stem}.docx"
        },
        "styles": {}, # Empty because we rely on the strict global styles
        "placeholders": {
            "standard": {},
            "runtime": {}
        },
        "layout": layout
    }
    
    output_path = Path(args.output)
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(config, f, indent=4)
        
    print(f"Successfully ingested {len(layout)} blocks into {output_path}")
    print("Review the JSON to ensure headers/footers were correctly excluded.")

if __name__ == "__main__":
    main()
