import argparse
from pypdf import PdfReader, PdfWriter

def split_pdf(input_pdf):
    try:
        reader = PdfReader(input_pdf)
        for i, page in enumerate(reader.pages):
            writer = PdfWriter()
            writer.add_page(page)
            output_filename = f"page_{i+1}.pdf"
            try:
                with open(output_filename, "wb") as output:
                    writer.write(output)
                print(f"Created {output_filename}")
            except Exception as e:
                print(f"Error writing to {output_filename}: {e}")
                return
        print(f"Successfully split {input_pdf} into {len(reader.pages)} pages.")
    except Exception as e:
        print(f"Error reading {input_pdf}: {e}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split a PDF document into individual pages.")
    parser.add_argument("input_pdf", help="The PDF file to split.")
    args = parser.parse_args()
    split_pdf(args.input_pdf)
