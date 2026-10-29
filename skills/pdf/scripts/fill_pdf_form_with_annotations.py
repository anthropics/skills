import json
import sys

from pypdf import PdfReader, PdfWriter
from pypdf.annotations import FreeText




def transform_from_image_coords(bbox, image_width, image_height, page):
    """Scale image pixels to the visible page, then convert to PDF coordinates."""
    crop = page.cropbox
    rotation = page.rotation % 360
    width = float(crop.width)
    height = float(crop.height)
    if rotation in (90, 270):
        width, height = height, width

    scaled = [
        bbox[0] * width / image_width,
        bbox[1] * height / image_height,
        bbox[2] * width / image_width,
        bbox[3] * height / image_height,
    ]
    return transform_from_pdf_coords(scaled, page)


def transform_from_pdf_coords(bbox, page):
    """Map visible top-left page coordinates to the PDF's bottom-left space."""
    x0, y0, x1, y1 = bbox
    crop = page.cropbox
    left, bottom = float(crop.left), float(crop.bottom)
    right, top = float(crop.right), float(crop.top)
    rotation = page.rotation % 360

    if rotation == 0:
        return left + x0, top - y1, left + x1, top - y0
    if rotation == 90:
        return left + y0, bottom + x0, left + y1, bottom + x1
    if rotation == 180:
        return right - x1, bottom + y0, right - x0, bottom + y1
    if rotation == 270:
        return right - y1, top - x1, right - y0, top - x0
    raise ValueError(f"Unsupported page rotation: {rotation}")


def fill_pdf_form(input_pdf_path, fields_json_path, output_pdf_path):
    
    with open(fields_json_path, "r") as f:
        fields_data = json.load(f)
    
    reader = PdfReader(input_pdf_path)
    writer = PdfWriter()
    
    writer.append(reader)
    
    annotations = []
    for field in fields_data["form_fields"]:
        page_num = field["page_number"]
        if not 1 <= page_num <= len(reader.pages):
            raise ValueError(f"Page {page_num} is outside the PDF's page range")

        page_info = next(p for p in fields_data["pages"] if p["page_number"] == page_num)
        page = reader.pages[page_num - 1]

        if "pdf_width" in page_info:
            transformed_entry_box = transform_from_pdf_coords(
                field["entry_bounding_box"],
                page,
            )
        else:
            image_width = page_info["image_width"]
            image_height = page_info["image_height"]
            transformed_entry_box = transform_from_image_coords(
                field["entry_bounding_box"],
                image_width, image_height,
                page,
            )
        
        if "entry_text" not in field or "text" not in field["entry_text"]:
            continue
        entry_text = field["entry_text"]
        text = entry_text["text"]
        if not text:
            continue
        
        font_name = entry_text.get("font", "Arial")
        font_size = str(entry_text.get("font_size", 14)) + "pt"
        font_color = entry_text.get("font_color", "000000")

        annotation = FreeText(
            text=text,
            rect=transformed_entry_box,
            font=font_name,
            font_size=font_size,
            font_color=font_color,
            border_color=None,
            background_color=None,
        )
        annotations.append(annotation)
        writer.add_annotation(page_number=page_num - 1, annotation=annotation)
        
    with open(output_pdf_path, "wb") as output:
        writer.write(output)
    
    print(f"Successfully filled PDF form and saved to {output_pdf_path}")
    print(f"Added {len(annotations)} text annotations")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: fill_pdf_form_with_annotations.py [input pdf] [fields.json] [output pdf]")
        sys.exit(1)
    input_pdf = sys.argv[1]
    fields_json = sys.argv[2]
    output_pdf = sys.argv[3]
    
    fill_pdf_form(input_pdf, fields_json, output_pdf)
