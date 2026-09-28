import os
import sys

from pdf2image import convert_from_path, pdfinfo_from_path


PAGE_BATCH_SIZE = 5


def convert(pdf_path, output_dir, max_dim=1000):
    page_count = int(pdfinfo_from_path(pdf_path)["Pages"])

    for first_page in range(1, page_count + 1, PAGE_BATCH_SIZE):
        last_page = min(first_page + PAGE_BATCH_SIZE - 1, page_count)
        images = convert_from_path(
            pdf_path, dpi=200, first_page=first_page, last_page=last_page
        )
        for page_number, image in enumerate(images, start=first_page):
            width, height = image.size
            if width > max_dim or height > max_dim:
                scale_factor = min(max_dim / width, max_dim / height)
                new_width = int(width * scale_factor)
                new_height = int(height * scale_factor)
                image = image.resize((new_width, new_height))

            image_path = os.path.join(output_dir, f"page_{page_number}.png")
            image.save(image_path)
            print(f"Saved page {page_number} as {image_path} (size: {image.size})")

    print(f"Converted {page_count} pages to PNG images")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert_pdf_to_images.py [input pdf] [output directory]")
        sys.exit(1)
    pdf_path = sys.argv[1]
    output_directory = sys.argv[2]
    convert(pdf_path, output_directory)
