"""Regression tests for issue #1883.

extract_form_field_info.py silently dropped every fillable text/choice
field whose widget annotation(s) live in /Kids: get_field_info() skipped
any field with /Kids unless it was a /Btn (radio-group candidate), so
parented /Tx and /Ch fields never reached the JSON output and
fill_fillable_fields.py then rejected them as invalid field IDs.

Tests build real PDFs with pypdf (no external fixtures, no network):
one form built two legal ways — terminal widgets vs parent + /Kid
widget — plus the issue's fixtures A-E, a parented /Sig exclusion
case, and a multi-widget parent. Run from the repo root or from
skills/pdf/scripts:

    python -m pytest skills/pdf/scripts/test_extract_form_field_info.py -v
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest
from pypdf import PdfReader, PdfWriter
from pypdf.generic import (
    ArrayObject,
    DecodedStreamObject,
    DictionaryObject,
    NameObject,
    NumberObject,
    TextStringObject,
)

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from extract_form_field_info import get_field_info, write_field_info  # noqa: E402


def _appearance_stream(writer, resources):
    stream = DecodedStreamObject()
    stream[NameObject("/Type")] = NameObject("/XObject")
    stream[NameObject("/Subtype")] = NameObject("/Form")
    stream[NameObject("/BBox")] = ArrayObject([NumberObject(0), NumberObject(0), NumberObject(10), NumberObject(10)])
    stream[NameObject("/Resources")] = resources
    stream.set_data(b"BT /Helv 10 Tf 0 g (x) Tj ET")
    return writer._add_object(stream)


def _resources(writer):
    font = writer._add_object(
        DictionaryObject(
            {
                NameObject("/Type"): NameObject("/Font"),
                NameObject("/Subtype"): NameObject("/Type1"),
                NameObject("/BaseFont"): NameObject("/Helvetica"),
            }
        )
    )
    return writer._add_object(
        DictionaryObject(
            {NameObject("/Font"): DictionaryObject({NameObject("/Helv"): font})}
        )
    )


def _widget(writer, resources, rect, parent_ref=None):
    widget = DictionaryObject(
        {
            NameObject("/Type"): NameObject("/Annot"),
            NameObject("/Subtype"): NameObject("/Widget"),
            NameObject("/Rect"): ArrayObject([NumberObject(x) for x in rect]),
            NameObject("/AP"): DictionaryObject(
                {NameObject("/N"): _appearance_stream(writer, resources)}
            ),
        }
    )
    if parent_ref is not None:
        widget[NameObject("/Parent")] = parent_ref
    return widget


def build_pdf(path, fields):
    """Build a one-page form PDF.

    fields: list of dicts with keys:
      name: qualified field name, e.g. "addr" or "shipping.name"
      ft: "/Tx", "/Ch", "/Btn" or "/Sig" (None for a grouping node)
      rect: [x0, y0, x1, y1]
      parented: bool — field dict holds /T /FT /Kids, widget holds /Rect /Parent
      options: list of (value, text) for /Ch
      widgets: how many widget annotations the field has (default 1)
    A grouping node is a field entry with ft=None and a "children" list of
    field dicts that share its name prefix.
    """
    writer = PdfWriter()
    page = writer.add_blank_page(612, 792)
    resources = _resources(writer)
    annots = []
    top_fields = []

    def add_field(spec, name_prefix=""):
        name = f"{name_prefix}{spec['name']}" if name_prefix else spec["name"]
        ft = spec.get("ft")
        rect = spec["rect"]
        widgets = []
        if spec.get("children"):
            # Grouping node: no /FT, /Kids are child field dicts. The
            # node ref is created first so each child field dict can
            # point back at it via /Parent (that is how pypdf builds
            # the qualified name, e.g. shipping.name).
            node_ref = writer._add_object(DictionaryObject({}))
            kid_refs = []
            for child in spec["children"]:
                kid_ref = add_field(child, name_prefix=f"{name}.")
                kid_ref.get_object()[NameObject("/Parent")] = node_ref
                kid_refs.append(kid_ref)
            node_ref.get_object().update(
                {
                    NameObject("/T"): TextStringObject(spec["name"]),
                    NameObject("/Kids"): ArrayObject(kid_refs),
                }
            )
            return node_ref
        if spec.get("parented"):
            field_ref = writer._add_object(DictionaryObject({}))
            for i in range(spec.get("widgets", 1)):
                r = rect if i == 0 else [rect[0], rect[1] - 40 * i, rect[2], rect[3] - 40 * i]
                w = _widget(writer, resources, r, parent_ref=field_ref)
                widgets.append(writer._add_object(w))
            field = DictionaryObject(
                {
                    NameObject("/T"): TextStringObject(spec["name"]),
                    NameObject("/FT"): NameObject(ft),
                    NameObject("/Kids"): ArrayObject(widgets),
                }
            )
            if spec.get("options"):
                field[NameObject("/Opt")] = ArrayObject(
                    [
                        ArrayObject([TextStringObject(v), TextStringObject(t)])
                        for v, t in spec["options"]
                    ]
                )
            # Fill in the pre-created ref so widgets can point at it.
            field_ref.update(field)
            annots.extend(widgets)
            return field_ref
        # Terminal widget: the field dict IS the widget annotation.
        w = _widget(writer, resources, rect)
        w[NameObject("/T")] = TextStringObject(spec["name"])
        w[NameObject("/FT")] = NameObject(ft)
        if spec.get("options"):
            w[NameObject("/Opt")] = ArrayObject(
                [
                    ArrayObject([TextStringObject(v), TextStringObject(t)])
                    for v, t in spec["options"]
                ]
            )
        ref = writer._add_object(w)
        annots.append(ref)
        return ref

    for spec in fields:
        top_fields.append(add_field(spec))

    form = DictionaryObject(
        {
            NameObject("/Fields"): ArrayObject(top_fields),
            NameObject("/DA"): TextStringObject("/Helv 10 Tf 0 g"),
            NameObject("/DR"): resources,
        }
    )
    writer._root_object[NameObject("/AcroForm")] = writer._add_object(form)
    page[NameObject("/Annots")] = ArrayObject(annots)
    with open(path, "wb") as f:
        writer.write(f)
    return path


ADDR = {"name": "addr", "ft": "/Tx", "rect": [92, 580, 260, 592]}
COUNTRY = {
    "name": "country",
    "ft": "/Ch",
    "rect": [92, 620, 260, 632],
    "options": [("/1", "USA"), ("/2", "Canada")],
}
AGREE = {"name": "agree", "ft": "/Btn", "rect": [92, 540, 110, 552]}


def _fields_by_id(pdf_path):
    reader = PdfReader(str(pdf_path))
    return {f["field_id"]: f for f in get_field_info(reader)}


def _parented(spec):
    return {**spec, "parented": True}


# --- Fixture A: terminal widgets, baseline (must be unchanged by the fix) ---


def test_terminal_text_and_button_extracted(tmp_path):
    pdf = build_pdf(tmp_path / "a.pdf", [ADDR, AGREE])
    fields = _fields_by_id(pdf)
    assert set(fields) == {"addr", "agree"}
    assert fields["addr"]["type"] == "text"
    assert fields["addr"]["page"] == 1
    assert fields["addr"]["rect"] == [92, 580, 260, 592]


def test_terminal_choice_extracted_with_options(tmp_path):
    pdf = build_pdf(tmp_path / "d.pdf", [COUNTRY, ADDR])
    fields = _fields_by_id(pdf)
    assert set(fields) == {"country", "addr"}
    assert fields["country"]["type"] == "choice"
    assert fields["country"]["choice_options"] == [
        {"value": "/1", "text": "USA"},
        {"value": "/2", "text": "Canada"},
    ]


# --- Fixtures B/C: parented /Tx and /Ch (the bug) ---


def test_parented_text_and_choice_extracted(tmp_path):
    pdf = build_pdf(tmp_path / "b.pdf", [_parented(ADDR), _parented(COUNTRY)])
    fields = _fields_by_id(pdf)
    assert set(fields) == {"addr", "country"}
    assert fields["addr"]["type"] == "text"
    assert fields["addr"]["page"] == 1
    assert fields["addr"]["rect"] == [92, 580, 260, 592]
    assert fields["country"]["type"] == "choice"
    assert fields["country"]["choice_options"] == [
        {"value": "/1", "text": "USA"},
        {"value": "/2", "text": "Canada"},
    ]


def test_parented_and_terminal_produce_same_field_info(tmp_path):
    """The two legal structures must extract to identical field info."""
    terminal = build_pdf(tmp_path / "terminal.pdf", [ADDR, COUNTRY])
    parented = build_pdf(tmp_path / "parented.pdf", [_parented(ADDR), _parented(COUNTRY)])
    reader_t = PdfReader(str(terminal))
    reader_p = PdfReader(str(parented))
    assert get_field_info(reader_t) == get_field_info(reader_p)


# --- Fixture E: nested grouping node ---


def test_nested_grouping_node_not_emitted(tmp_path):
    pdf = build_pdf(
        tmp_path / "e.pdf",
        [
            {
                "name": "shipping",
                "ft": None,
                "rect": [92, 580, 260, 592],
                "children": [{"name": "name", "ft": "/Tx", "rect": [92, 580, 260, 592], "parented": True}],
            }
        ],
    )
    fields = _fields_by_id(pdf)
    assert set(fields) == {"shipping.name"}
    assert fields["shipping.name"]["type"] == "text"
    assert fields["shipping.name"]["page"] == 1


# --- Scope boundaries (deliberate, not failures) ---


def test_parented_sig_field_stays_excluded(tmp_path):
    """Parented /Sig is not a supported fillable type: it must stay
    excluded, so no new unvalidated filling path is created. Terminal
    /Sig behaviour is pre-existing and out of scope."""
    sig = {"name": "sig", "ft": "/Sig", "rect": [92, 580, 260, 592]}
    pdf = build_pdf(tmp_path / "sig.pdf", [_parented(sig), ADDR])
    fields = _fields_by_id(pdf)
    assert set(fields) == {"addr"}


def test_parented_field_with_two_widgets_is_one_entry(tmp_path):
    """One logical field with two widget kids: exactly one entry, whose
    page/rect is one of its widgets (the schema holds a single rect)."""
    spec = {**ADDR, "parented": True, "widgets": 2}
    pdf = build_pdf(tmp_path / "multi.pdf", [spec])
    fields = _fields_by_id(pdf)
    assert set(fields) == {"addr"}
    assert fields["addr"]["rect"] in ([92, 580, 260, 592], [92, 540, 260, 552])
    assert fields["addr"]["page"] == 1


def test_parented_button_keeps_radio_group_behaviour(tmp_path):
    """A parented /Btn is still handled as a radio-group candidate,
    exactly as before — button classification is out of scope."""
    pdf = build_pdf(tmp_path / "btn.pdf", [_parented(AGREE), ADDR])
    fields = _fields_by_id(pdf)
    assert "addr" in fields
    assert fields["addr"]["type"] == "text"
    # The button itself is not emitted as a plain checkbox field.
    assert "agree" not in fields


# --- End-to-end: extraction + filling ---


def test_end_to_end_fill_parented_form(tmp_path):
    pdf = build_pdf(tmp_path / "fill.pdf", [_parented(ADDR), _parented(COUNTRY)])
    json_path = tmp_path / "fields.json"
    write_field_info(str(pdf), str(json_path))
    extracted = json.loads(json_path.read_text())
    assert {f["field_id"] for f in extracted} == {"addr", "country"}

    values = tmp_path / "values.json"
    values.write_text(
        json.dumps(
            [
                {"field_id": "addr", "description": "address", "page": 1, "value": "123 Main St"},
                {"field_id": "country", "description": "country", "page": 1, "value": "/1"},
            ]
        )
    )
    out_pdf = tmp_path / "filled.pdf"
    proc = subprocess.run(
        [sys.executable, str(SCRIPTS / "fill_fillable_fields.py"), str(pdf), str(values), str(out_pdf)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    filled = PdfReader(str(out_pdf)).get_fields()
    assert filled["addr"].get("/V") == "123 Main St"
    assert filled["country"].get("/V") == "/1"


def test_end_to_end_fill_nested_grouping_value_lands_on_leaf(tmp_path):
    pdf = build_pdf(
        tmp_path / "fill_e.pdf",
        [
            {
                "name": "shipping",
                "ft": None,
                "rect": [92, 580, 260, 592],
                "children": [{"name": "name", "ft": "/Tx", "rect": [92, 580, 260, 592], "parented": True}],
            }
        ],
    )
    json_path = tmp_path / "fields.json"
    write_field_info(str(pdf), str(json_path))
    extracted = json.loads(json_path.read_text())
    assert [f["field_id"] for f in extracted] == ["shipping.name"]

    values = tmp_path / "values.json"
    values.write_text(
        json.dumps(
            [{"field_id": "shipping.name", "description": "name", "page": 1, "value": "Homer"}]
        )
    )
    out_pdf = tmp_path / "filled.pdf"
    proc = subprocess.run(
        [sys.executable, str(SCRIPTS / "fill_fillable_fields.py"), str(pdf), str(values), str(out_pdf)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    filled = PdfReader(str(out_pdf)).get_fields()
    assert filled["shipping.name"].get("/V") == "Homer"
