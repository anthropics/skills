import sys
import os
from docxcompose.composer import Composer
from docx import Document

def merge_docs(cover_path, body_path, output_path):
    if not os.path.exists(cover_path):
        print(f"Error: Cover file not found at {cover_path}")
        return
    if not os.path.exists(body_path):
        print(f"Error: Body file not found at {body_path}")
        return

    master = Document(cover_path)
    composer = Composer(master)
    
    doc2 = Document(body_path)
    # Appending doc2 to master. 
    # Note: We do NOT force a page break here. 
    # If the cover page needs a break, it should be in the cover doc.
    # If the body needs to start on a new page, it should have a break at the start.
    composer.append(doc2)
    
    composer.save(output_path)
    print(f"Merged document saved to {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python merge_docs.py <cover_path> <body_path> <output_path>")
        sys.exit(1)
    
    merge_docs(sys.argv[1], sys.argv[2], sys.argv[3])
