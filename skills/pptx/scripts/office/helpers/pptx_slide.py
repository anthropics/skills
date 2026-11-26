"""Find the slide-XML defects known or predicted to make PowerPoint refuse or repair the file.

Schema errors are picked by a denylist over lxml's messages, so an unrecognised
error class is a miss rather than a false alarm. Animations that name a shape
the slide no longer has are found by reading the part.
"""


from __future__ import annotations

import re

SLIDE_PART_RE = re.compile(
    r"ppt/(slides|slideLayouts|slideMasters|notesSlides|notesMasters|handoutMasters)"
    r"/[^/]+\.xml"
)

FATAL_SLIDE_ERRORS: tuple[tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(r"\}tableStyleId': This element is not expected"),
        "two <a:tableStyleId> in one <a:tblPr> (the schema allows one)",
    ),
    (
        re.compile(r"\}srgbClr', attribute 'val'"),
        "a colour that is not six hex digits",
    ),
    (
        re.compile(r"\}txBody': Missing child element"),
        "a <p:txBody> with no children",
    ),
    (
        re.compile(r"\}miter', attribute 'lim'"),
        'a line join with lim="NaN"',
    ),
    (
        re.compile(r"\}uLnTx': This element is not expected"),
        "<a:uLnTx> in a position the schema forbids",
    ),
    (
        re.compile(r"\}overrideClrMapping': This element is not expected"),
        "<p:overrideClrMapping> in a position the schema forbids",
    ),
    (
        re.compile(r"\}nvGrpSpPr': Missing child element"),
        "a <p:nvGrpSpPr> with no children",
    ),
    (
        re.compile(r"\}(?:off|ext|chOff|chExt)', attribute '\w+': '-?(?:Infinity|NaN)'"),
        "a position or size that is not a number (check the x, y, w, h you worked out)",
    ),
    (
        re.compile(r"\}prstDash', attribute 'val'"),
        "an unknown line dash style (for line.dashType try dash, sysDash or solid)",
    ),
)


def is_schema_verdict(error: str) -> bool:
    return error.startswith("Element ")


_PML = "{http://schemas.openxmlformats.org/presentationml/2006/main}"
_MC = "{http://schemas.openxmlformats.org/markup-compatibility/2006}"

_NAMES_A_SHAPE = frozenset({f"{_PML}spTgt", f"{_PML}bldP", f"{_PML}bldGraphic"})


def _shape_id(value: str | None) -> int | str | None:
    text = (value or "").strip()
    if text.isascii() and text.isdigit() and len(text) <= 18:
        return int(text)
    return text or None


def stranded_animation_targets(root) -> list[str]:
    timing = root.find(f"{_PML}timing")
    if timing is None:
        timing = root.find(f"{_MC}AlternateContent/{_MC}Choice/{_PML}timing")
    if timing is None:
        return []

    on_slide = {_shape_id(e.get("id")) for e in root.iter("{*}cNvPr")}
    named = {_shape_id(e.get("spid")) for e in timing.iter(*_NAMES_A_SHAPE)} - {None}
    stranded = named - on_slide
    return [
        f"<p:timing> animates shape id {spid if isinstance(spid, int) else repr(spid[:16])}, which is gone, so PowerPoint will "
        f"offer to repair the deck. Fix: delete the slide's whole <p:timing> element "
        f"(the slide loses its animations), or put the shape back"
        for spid in sorted(stranded, key=str)
    ]


def fatal_slide_errors(errors: set[str]) -> list[str]:
    out = []
    for error in sorted(errors):
        for pattern, meaning in FATAL_SLIDE_ERRORS:
            if pattern.search(error):
                out.append(f"{meaning}: {error}")
                break
    return out
