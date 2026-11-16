"""Print each slide of a .pptx, .pptm, .potx or .ppsx as markdown under `<!-- Slide number: N -->`.

Title, text, tables, chart data, picture alt text and speaker notes; shapes top to bottom.

Usage: python slide_text.py deck.pptx
"""

import os
import re
import sys
import zipfile

from pptx.package import Package


def _position(shape):
    try:
        return (shape.top or 0, shape.left or 0)
    except Exception:
        return (0, 0)


def _one_line(text) -> str:
    return " ".join(str(text).split())


def _table(rows) -> list[str]:
    lines = ["| " + " | ".join(_one_line(c).replace("|", "\\|") for c in r) + " |" for r in rows]
    if lines:
        lines.insert(1, "|" + " --- |" * len(rows[0]))
    return lines


def _chart(chart) -> list[str]:
    heading = "### Chart"
    try:
        if chart.has_title and chart.chart_title.has_text_frame:
            heading += ": " + _one_line(chart.chart_title.text_frame.text)
        categories = [c.label for c in chart.plots[0].categories]
        series = [(s.name, list(s.values)) for s in chart.series]
    except Exception as e:
        return [
            heading,
            f"[chart data not readable ({type(e).__name__}): render the slide to see it]",
        ]
    rows = [["Category", *(name for name, _ in series)]]
    for i, category in enumerate(categories):
        rows.append([category, *(v[i] if i < len(v) else "" for _, v in series)])
    return [heading, "", *_table(rows)]


def _shape(shape) -> list[str]:
    tag = shape._element.tag
    if tag.endswith("}grpSp"):
        return _shapes(shape.shapes)
    if tag.endswith("}pic"):
        alt = _one_line(shape._element._nvXxPr.cNvPr.get("descr", ""))
        return [f"![{alt}]({shape.name})"]
    if getattr(shape, "has_table", False):
        return ["", *_table([[c.text for c in r.cells] for r in shape.table.rows]), ""]
    if getattr(shape, "has_chart", False):
        return ["", *_chart(shape.chart), ""]
    if shape.has_text_frame and shape.text_frame.text.strip():
        text = shape.text_frame.text.replace("\v", "\n")
        is_title = shape.is_placeholder and shape.placeholder_format.idx == 0
        return ["# " + text.lstrip() if is_title else text]
    return []


def _members(shapes) -> list:
    try:
        return list(shapes)
    except Exception:
        pass
    members = []
    for i in range(len(shapes)):
        try:
            members.append(shapes[i])
        except Exception as e:
            members.append(e)
    return members


def _shapes(shapes) -> list[str]:
    lines = []
    for shape in sorted(_members(shapes), key=_position):
        try:
            if isinstance(shape, Exception):
                raise shape
            lines += _shape(shape)
        except Exception as e:
            lines.append(f"[shape not readable ({type(e).__name__}): render the slide to see it]")
    return lines


def slide_text(slide, number: int) -> str:
    lines = [f"<!-- Slide number: {number} -->", *_shapes(slide.shapes)]
    try:
        notes = slide.notes_slide.notes_text_frame if slide.has_notes_slide else None
        if notes is not None and notes.text.strip():
            lines += ["", "### Notes:", notes.text.replace("\v", "\n")]
    except Exception as e:
        lines += ["", f"[notes not readable ({type(e).__name__})]"]
    return re.sub(r"\n{3,}", "\n\n", "\n".join(lines).strip())


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit("Usage: python slide_text.py deck.pptx")
    path = sys.argv[1]
    if not os.path.isfile(path):
        sys.exit(f"Error: {path} {'is not a file' if os.path.exists(path) else 'does not exist'}")
    if not zipfile.is_zipfile(path):
        sys.exit(
            f"Error: {path} is corrupt, password-protected, or an old .ppt (not a zip archive)"
        )
    try:
        deck = getattr(Package.open(path).main_document_part, "presentation", None)
    except Exception as e:
        sys.exit(f"Error: cannot read {path}: {e}")
    if deck is None:
        sys.exit(f"Error: {path} is not a .pptx, .pptm, .potx or .ppsx file")
    sys.stdout.reconfigure(errors="replace")
    try:
        blocks = [slide_text(s, n) for n, s in enumerate(deck.slides, 1)]
        print("\n\n".join(blocks) or "[no slides; layouts and masters are not printed]", flush=True)
    except BrokenPipeError:
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())


if __name__ == "__main__":
    main()
