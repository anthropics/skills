import argparse
from pypdf import PdfWriter, PdfReader

def merge_pdfs(pdf_files, output_pdf):
    writer = PdfWriter()
    for pdf_file in pdf_files:
        try:
            reader = PdfReader(pdf_file)
            for page in reader.pages:
                writer.add_page(page)
        except Exception as e:
            print(f"Error reading {pdf_file}: {e}")
            return
    try:
        with open(output_pdf, "wb") as output:
            writer.write(output)
        print(f"Successfully merged {len(pdf_files)} PDF files into {output_pdf}")
    except Exception as e:
        print(f"Error writing to {output_pdf}: {e}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Merge multiple PDF documents into a single file.")
    parser.add_argument("pdf_files", nargs='+', help="The PDF files to merge.")
    parser.add_argument("-o", "--output", default="merged.pdf", help="The name of the output PDF file.")
    args = parser.parse_args()
    if len(args.pdf_files) < 2:
        print("You must provide at least two PDF files to merge.")
    else:
        merge_pdfs(args.pdf_files, args.output)
