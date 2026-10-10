import sys
import os
from pathlib import Path

def verify_visual(docx_path):
    print(f"--- Visual Verification Check ---")
    print(f"Target: {docx_path}")
    
    if not os.path.exists(docx_path):
        print("Error: File does not exist.")
        return

    try:
        # Attempt to use docx2pdf if available (Windows/Word required)
        from docx2pdf import convert
        pdf_path = str(Path(docx_path).with_suffix('.pdf'))
        print(f"Attempting PDF conversion to: {pdf_path}")
        convert(docx_path, pdf_path)
        print(f"[SUCCESS] PDF created. Please open {pdf_path} to visually verify layout.")
        
        # Future: Add image comparison here if libraries allowed
        
    except ImportError:
        print("[WARNING] 'docx2pdf' library not found. Cannot generate PDF for visual check.")
        print("To enable this, run: pip install docx2pdf")
        print("Note: This requires Microsoft Word to be installed on the machine.")
    except Exception as e:
        print(f"[ERROR] PDF conversion failed: {e}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python verify_visual.py <path_to_docx>")
    else:
        verify_visual(sys.argv[1])
