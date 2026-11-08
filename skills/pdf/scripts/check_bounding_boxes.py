from dataclasses import dataclass
import json
import sys




@dataclass
class RectAndField:
    rect: list[float]
    rect_type: str
    field: dict


def get_bounding_box_messages(fields_json_stream) -> list[str]:
    messages = []
    fields = json.load(fields_json_stream)
    messages.append(f"Read {len(fields['form_fields'])} fields")
    page_sizes = {}
    for page in fields.get("pages", []):
        if "pdf_width" in page and "pdf_height" in page:
            page_sizes[page["page_number"]] = (page["pdf_width"], page["pdf_height"])
        elif "image_width" in page and "image_height" in page:
            page_sizes[page["page_number"]] = (page["image_width"], page["image_height"])

    def rects_intersect(r1, r2):
        disjoint_horizontal = r1[0] >= r2[2] or r1[2] <= r2[0]
        disjoint_vertical = r1[1] >= r2[3] or r1[3] <= r2[1]
        return not (disjoint_horizontal or disjoint_vertical)

    rects_and_fields = []
    for f in fields["form_fields"]:
        rects_and_fields.append(RectAndField(f["label_bounding_box"], "label", f))
        rects_and_fields.append(RectAndField(f["entry_bounding_box"], "entry", f))

    has_error = False
    for i, ri in enumerate(rects_and_fields):
        x0, y0, x1, y1 = ri.rect
        page_number = ri.field["page_number"]
        if x0 >= x1 or y0 >= y1:
            has_error = True
            messages.append(
                f"FAILURE: {ri.rect_type} bounding box for `{ri.field['description']}` "
                f"must have x0 < x1 and y0 < y1: {ri.rect}"
            )
        elif page_number in page_sizes:
            width, height = page_sizes[page_number]
            if not (0 <= x0 < x1 <= width and 0 <= y0 < y1 <= height):
                has_error = True
                messages.append(
                    f"FAILURE: {ri.rect_type} bounding box for `{ri.field['description']}` "
                    f"is outside page {page_number} ({width}x{height}): {ri.rect}"
                )
        if len(messages) >= 20:
            messages.append("Aborting further checks; fix bounding boxes and try again")
            return messages

        for j in range(i + 1, len(rects_and_fields)):
            rj = rects_and_fields[j]
            if ri.field["page_number"] == rj.field["page_number"] and rects_intersect(ri.rect, rj.rect):
                has_error = True
                if ri.field is rj.field:
                    messages.append(f"FAILURE: intersection between label and entry bounding boxes for `{ri.field['description']}` ({ri.rect}, {rj.rect})")
                else:
                    messages.append(f"FAILURE: intersection between {ri.rect_type} bounding box for `{ri.field['description']}` ({ri.rect}) and {rj.rect_type} bounding box for `{rj.field['description']}` ({rj.rect})")
                if len(messages) >= 20:
                    messages.append("Aborting further checks; fix bounding boxes and try again")
                    return messages
        if ri.rect_type == "entry":
            if "entry_text" in ri.field:
                font_size = ri.field["entry_text"].get("font_size", 14)
                entry_height = ri.rect[3] - ri.rect[1]
                if entry_height < font_size:
                    has_error = True
                    messages.append(f"FAILURE: entry bounding box height ({entry_height}) for `{ri.field['description']}` is too short for the text content (font size: {font_size}). Increase the box height or decrease the font size.")
                    if len(messages) >= 20:
                        messages.append("Aborting further checks; fix bounding boxes and try again")
                        return messages

    if not has_error:
        messages.append("SUCCESS: All bounding boxes are valid")
    return messages

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: check_bounding_boxes.py [fields.json]")
        sys.exit(1)
    with open(sys.argv[1]) as f:
        messages = get_bounding_box_messages(f)
    for msg in messages:
        print(msg)
