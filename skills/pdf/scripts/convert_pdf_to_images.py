import os
import sys
from tempfile import TemporaryDirectory

from PIL import Image
from pdf2image import convert_from_path


def convert(pdf_path, output_dir, max_dim=1000):
    # Let Poppler write rendered pages to disk so a long PDF does not require
    # every page's pixel data to remain in memory at once.
    with TemporaryDirectory(prefix="pdf-pages-") as temp_dir:
        image_paths = convert_from_path(
            pdf_path,
            dpi=200,
            output_folder=temp_dir,
            paths_only=True,
        )

        for i, rendered_path in enumerate(image_paths):
            image_path = os.path.join(output_dir, f"page_{i+1}.png")
            with Image.open(rendered_path) as image:
                width, height = image.size
                if width > max_dim or height > max_dim:
                    scale_factor = min(max_dim / width, max_dim / height)
                    new_width = int(width * scale_factor)
                    new_height = int(height * scale_factor)
                    resized = image.resize((new_width, new_height))
                    try:
                        resized.save(image_path)
                        size = resized.size
                    finally:
                        resized.close()
                else:
                    image.save(image_path)
                    size = image.size
            print(f"Saved page {i+1} as {image_path} (size: {size})")

    print(f"Converted {len(image_paths)} pages to PNG images")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert_pdf_to_images.py [input pdf] [output directory]")
        sys.exit(1)
    pdf_path = sys.argv[1]
    output_directory = sys.argv[2]
    convert(pdf_path, output_directory)
