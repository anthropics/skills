import json
import sys

from PIL import Image, ImageDraw




def create_validation_image(page_number, fields_json_path, input_path, output_path):
    with open(fields_json_path, 'r') as f:
        data = json.load(f)

    page = next(p for p in data["pages"] if p["page_number"] == page_number)
    if "pdf_width" in page:
        source_width, source_height = page["pdf_width"], page["pdf_height"]
    else:
        source_width, source_height = page["image_width"], page["image_height"]
    if source_width <= 0 or source_height <= 0:
        raise ValueError("Page dimensions must be positive")

    with Image.open(input_path) as img:
        x_scale = img.width / source_width
        y_scale = img.height / source_height
        draw = ImageDraw.Draw(img)
        num_boxes = 0

        def image_box(box):
            return [
                box[0] * x_scale,
                box[1] * y_scale,
                box[2] * x_scale,
                box[3] * y_scale,
            ]

        for field in data["form_fields"]:
            if field["page_number"] == page_number:
                entry_box = image_box(field['entry_bounding_box'])
                label_box = image_box(field['label_bounding_box'])
                draw.rectangle(entry_box, outline='red', width=2)
                draw.rectangle(label_box, outline='blue', width=2)
                num_boxes += 2

        img.save(output_path)
    print(f"Created validation image at {output_path} with {num_boxes} bounding boxes")


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print("Usage: create_validation_image.py [page number] [fields.json file] [input image path] [output image path]")
        sys.exit(1)
    page_number = int(sys.argv[1])
    fields_json_path = sys.argv[2]
    input_image_path = sys.argv[3]
    output_image_path = sys.argv[4]
    create_validation_image(page_number, fields_json_path, input_image_path, output_image_path)
