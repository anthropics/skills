from dataclasses import dataclass
from collections import defaultdict
import json
import sys


# Script to check that the `fields.json` file that Claude creates when analyzing PDFs
# does not have overlapping bounding boxes. See forms.md.


@dataclass
class RectAndField:
    rect: list[float]
    rect_type: str
    field: dict


# Returns a list of messages that are printed to stdout for Claude to read.
def get_bounding_box_messages(fields_json_stream) -> list[str]:
    messages = []
    fields = json.load(fields_json_stream)
    messages.append(f"Read {len(fields['form_fields'])} fields")

    def rects_intersect(r1, r2):
        disjoint_horizontal = r1[0] >= r2[2] or r1[2] <= r2[0]
        disjoint_vertical = r1[1] >= r2[3] or r1[3] <= r2[1]
        return not (disjoint_horizontal or disjoint_vertical)

    # Group bounding boxes by page number to reduce comparisons
    # This optimization significantly improves performance for multi-page forms
    boxes_by_page = defaultdict(list)
    for f in fields["form_fields"]:
        page = f["page_number"]
        boxes_by_page[page].append(RectAndField(f["label_bounding_box"], "label", f))
        boxes_by_page[page].append(RectAndField(f["entry_bounding_box"], "entry", f))

    has_error = False
    # Only compare boxes within the same page (boxes on different pages can't overlap)
    for page, page_boxes in boxes_by_page.items():
        for i, ri in enumerate(page_boxes):
            for j in range(i + 1, len(page_boxes)):
                rj = page_boxes[j]
                if rects_intersect(ri.rect, rj.rect):
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
    # Input file should be in the `fields.json` format described in forms.md.
    with open(sys.argv[1]) as f:
        messages = get_bounding_box_messages(f)
    for msg in messages:
        print(msg)
