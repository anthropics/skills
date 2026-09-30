import sys
from docx import Document
from docx.enum.text import WD_ALIGN_PARAGRAPH

def audit_docx(file_path):
    print(f"--- Style Audit: {file_path} ---")
    try:
        doc = Document(file_path)
    except Exception as e:
        print(f"Error opening file: {e}")
        return

    print(f"{'Para #':<8} | {'Style':<15} | {'Font':<20} | {'Size':<6} | {'Align':<10} | {'Text Preview'}")
    print("-" * 90)

    for i, p in enumerate(doc.paragraphs):
        if not p.text.strip():
            continue
            
        # Get effective style
        style = p.style.name
        
        # Get formatting from runs (first run usually dictates visual style if manual)
        font_name = "Default"
        font_size = "Default"
        if p.runs:
            r = p.runs[0]
            if r.font.name: font_name = r.font.name
            if r.font.size: font_size = str(r.font.size.pt)
            
        # Alignment
        align_map = {
            WD_ALIGN_PARAGRAPH.LEFT: "Left",
            WD_ALIGN_PARAGRAPH.CENTER: "Center",
            WD_ALIGN_PARAGRAPH.RIGHT: "Right",
            WD_ALIGN_PARAGRAPH.JUSTIFY: "Justify"
        }
        align = align_map.get(p.alignment, "Left (Def)")
        
        preview = (p.text[:30] + '...') if len(p.text) > 30 else p.text
        
        print(f"{i+1:<8} | {style:<15} | {font_name:<20} | {font_size:<6} | {align:<10} | {preview}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python style_audit.py <docx_file>")
    else:
        audit_docx(sys.argv[1])
