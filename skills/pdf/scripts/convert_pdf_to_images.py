import sys
from pathlib import Path

from pdf2image import convert_from_path
from PIL import Image


def convert(pdf_path, output_dir, max_dim=1000):
    pdf_path = Path(pdf_path)
    output_dir = Path(output_dir)

    if not pdf_path.is_file():
        raise FileNotFoundError(f"PDF not found: {pdf_path}")

    output_dir.mkdir(parents=True, exist_ok=True)
    images = convert_from_path(pdf_path, dpi=200)

    for i, image in enumerate(images):
        width, height = image.size
        if width > max_dim or height > max_dim:
            scale_factor = max_dim / max(width, height)
            new_size = (int(width * scale_factor), int(height * scale_factor))
            image = image.resize(new_size, Image.LANCZOS)

        image_path = output_dir / f"page_{i + 1}.png"
        image.save(image_path)
        print(f"Saved page {i + 1} as {image_path} (size: {image.size})")

    print(f"Converted {len(images)} pages to PNG images")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert_pdf_to_images.py [input pdf] [output directory]")
        sys.exit(1)
    pdf_path = sys.argv[1]
    output_directory = sys.argv[2]
    convert(pdf_path, output_directory)
