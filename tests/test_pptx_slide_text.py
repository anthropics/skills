import importlib.util
from pathlib import Path
import subprocess
import sys

from pptx import Presentation
from pptx.oxml import parse_xml


def _load_slide_text():
    scripts_dir = Path(__file__).resolve().parents[1] / "skills" / "pptx" / "scripts"
    spec = importlib.util.spec_from_file_location("slide_text", scripts_dir / "slide_text.py")
    module = importlib.util.module_from_spec(spec)
    assert spec is not None and spec.loader is not None
    spec.loader.exec_module(module)
    return module


slide_text = _load_slide_text()
PML_NS = "http://schemas.openxmlformats.org/presentationml/2006/main"


def test_structured_deck_nonzero_idx_title_placeholder_renders_as_heading():
    prs = Presentation()
    slide = prs.slides.add_slide(prs.slide_layouts[6])

    title_box = slide.shapes.add_textbox(457200, 365760, 8229600, 731520)
    title_box._element.nvSpPr.nvPr.append(
        parse_xml(f'<p:ph xmlns:p="{PML_NS}" idx="100" type="title" hasCustomPrompt="1"/>')
    )
    title_box.text_frame.text = "Quarterly Results"

    body_box = slide.shapes.add_textbox(457200, 1371600, 8229600, 3200400)
    body_box._element.nvSpPr.nvPr.append(
        parse_xml(f'<p:ph xmlns:p="{PML_NS}" idx="101" type="body" hasCustomPrompt="1"/>')
    )
    body_box.text_frame.text = "Revenue grew 25% year over year"

    assert slide_text.slide_text(slide, 1) == (
        "<!-- Slide number: 1 -->\n"
        "# Quarterly Results\n"
        "Revenue grew 25% year over year"
    )


def test_slide_placeholder_inherits_title_type_from_layout_with_nonzero_idx():
    prs = Presentation()
    layout = prs.slide_layouts[0]
    layout.placeholders[0]._element.ph.set("idx", "15")

    slide = prs.slides.add_slide(layout)
    slide.placeholders[15].text = "Section Divider"
    del slide.placeholders[15]._element.ph.attrib["type"]

    assert slide_text.slide_text(slide, 1) == (
        "<!-- Slide number: 1 -->\n"
        "# Section Divider"
    )


def test_unindexed_non_title_placeholder_is_not_rendered_as_heading():
    prs = Presentation()
    slide = prs.slides.add_slide(prs.slide_layouts[6])

    body_box = slide.shapes.add_textbox(457200, 1371600, 8229600, 3200400)
    body_box._element.nvSpPr.nvPr.append(
        parse_xml(f'<p:ph xmlns:p="{PML_NS}" type="body"/>')
    )
    body_box.text_frame.text = "Body paragraph without explicit idx"

    footer_box = slide.shapes.add_textbox(457200, 6000000, 8229600, 400000)
    footer_box._element.nvSpPr.nvPr.append(
        parse_xml(f'<p:ph xmlns:p="{PML_NS}" type="ftr"/>')
    )
    footer_box.text_frame.text = "Confidential"

    assert slide_text.slide_text(slide, 1) == (
        "<!-- Slide number: 1 -->\n"
        "Body paragraph without explicit idx\n"
        "Confidential"
    )


def test_standard_powerpoint_title_and_content_cli_output(tmp_path: Path):
    prs = Presentation()
    slide = prs.slides.add_slide(prs.slide_layouts[1])
    slide.shapes.title.text = "Standard Title"
    slide.shapes.title._element.ph.attrib.clear()
    slide.placeholders[1].text = "Bullet item"

    deck_path = tmp_path / "deck.pptx"
    prs.save(str(deck_path))

    script = Path(__file__).resolve().parents[1] / "skills" / "pptx" / "scripts" / "slide_text.py"
    res = subprocess.run(
        [sys.executable, str(script), str(deck_path)],
        capture_output=True,
        text=True,
        check=True,
    )
    assert res.stdout.strip() == (
        "<!-- Slide number: 1 -->\n"
        "# Standard Title\n"
        "Bullet item"
    )
