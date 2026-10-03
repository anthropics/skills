import sys
import types
from pathlib import Path

import pytest

# Ensure scripts and office modules can be imported
scripts_dir = Path(__file__).parent.parent / "scripts"
if str(scripts_dir) not in sys.path:
    sys.path.insert(0, str(scripts_dir))

# Mock defusedxml if not present in test environment
try:
    import defusedxml.minidom
except ImportError:
    import xml.dom.minidom
    mock_defused = types.ModuleType("defusedxml")
    mock_defused.minidom = xml.dom.minidom
    sys.modules["defusedxml"] = mock_defused
    sys.modules["defusedxml.minidom"] = xml.dom.minidom

from clean import RefusedToClean, get_slides_in_sldidlst, remove_orphaned_slides


def test_missing_presentation_xml_refuses_to_clean(tmp_path):
    """When presentation.xml is missing, slides on disk must not be deleted."""
    slides_dir = tmp_path / "ppt" / "slides"
    slides_dir.mkdir(parents=True)
    slide1 = slides_dir / "slide1.xml"
    slide1.write_text("<xml/>", encoding="utf-8")

    with pytest.raises(RefusedToClean, match="presentation.xml is missing"):
        remove_orphaned_slides(tmp_path)

    assert slide1.exists()


def test_malformed_presentation_xml_refuses_to_clean(tmp_path):
    """When presentation.xml is malformed, slides on disk must not be deleted."""
    slides_dir = tmp_path / "ppt" / "slides"
    slides_dir.mkdir(parents=True)
    slide1 = slides_dir / "slide1.xml"
    slide1.write_text("<xml/>", encoding="utf-8")

    ppt_dir = tmp_path / "ppt"
    pres_path = ppt_dir / "presentation.xml"
    pres_path.write_text("<unclosed_tag>", encoding="utf-8")

    rels_dir = ppt_dir / "_rels"
    rels_dir.mkdir(parents=True)
    rels_content = """<?xml version="1.0" encoding="UTF-8"?>
    <Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
        <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide" Target="slides/slide1.xml"/>
    </Relationships>"""
    (rels_dir / "presentation.xml.rels").write_text(rels_content, encoding="utf-8")

    with pytest.raises(RefusedToClean, match="Failed to parse"):
        remove_orphaned_slides(tmp_path)

    assert slide1.exists()


def test_single_quoted_attributes_parsed(tmp_path):
    """Ensure single-quoted XML attributes in presentation.xml are properly parsed."""
    ppt_dir = tmp_path / "ppt"
    slides_dir = ppt_dir / "slides"
    slides_dir.mkdir(parents=True)
    slide1 = slides_dir / "slide1.xml"
    slide1.write_text("<xml/>", encoding="utf-8")
    orphan = slides_dir / "slide2.xml"
    orphan.write_text("<xml/>", encoding="utf-8")

    rels_dir = ppt_dir / "_rels"
    rels_dir.mkdir(parents=True)
    rels_content = """<?xml version="1.0" encoding="UTF-8"?>
    <Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
        <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide" Target="slides/slide1.xml"/>
    </Relationships>"""
    (rels_dir / "presentation.xml.rels").write_text(rels_content, encoding="utf-8")

    pres_content = """<?xml version="1.0" encoding="UTF-8"?>
    <p:presentation xmlns:p="http://schemas.openxmlformats.org/presentationml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
        <p:sldIdLst>
            <p:sldId id='256' r:id='rId1'/>
        </p:sldIdLst>
    </p:presentation>"""
    (ppt_dir / "presentation.xml").write_text(pres_content, encoding="utf-8")

    referenced = get_slides_in_sldidlst(tmp_path)
    assert referenced == {"slide1.xml"}

    removed = remove_orphaned_slides(tmp_path)
    assert slide1.exists()
    assert not orphan.exists()
    assert str(Path("ppt/slides/slide2.xml")) in [str(Path(r)) for r in removed]


def test_alternative_namespace_prefix_parsed(tmp_path):
    """Ensure alternative namespace prefixes (e.g. ppt:sldId) are properly parsed."""
    ppt_dir = tmp_path / "ppt"
    slides_dir = ppt_dir / "slides"
    slides_dir.mkdir(parents=True)
    slide1 = slides_dir / "slide1.xml"
    slide1.write_text("<xml/>", encoding="utf-8")

    rels_dir = ppt_dir / "_rels"
    rels_dir.mkdir(parents=True)
    rels_content = """<?xml version="1.0" encoding="UTF-8"?>
    <Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
        <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide" Target="slides/slide1.xml"/>
    </Relationships>"""
    (rels_dir / "presentation.xml.rels").write_text(rels_content, encoding="utf-8")

    pres_content = """<?xml version="1.0" encoding="UTF-8"?>
    <ppt:presentation xmlns:ppt="http://schemas.openxmlformats.org/presentationml/2006/main" xmlns:rel="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
        <ppt:sldIdLst>
            <ppt:sldId id="256" rel:id="rId1"/>
        </ppt:sldIdLst>
    </ppt:presentation>"""
    (ppt_dir / "presentation.xml").write_text(pres_content, encoding="utf-8")

    referenced = get_slides_in_sldidlst(tmp_path)
    assert referenced == {"slide1.xml"}


def test_zero_matching_slides_refuses_to_clean(tmp_path):
    """When presentation.xml references rIds that don't match any on-disk slides, refuse to clean."""
    ppt_dir = tmp_path / "ppt"
    slides_dir = ppt_dir / "slides"
    slides_dir.mkdir(parents=True)
    slide1 = slides_dir / "slide1.xml"
    slide1.write_text("<xml/>", encoding="utf-8")

    rels_dir = ppt_dir / "_rels"
    rels_dir.mkdir(parents=True)
    rels_content = """<?xml version="1.0" encoding="UTF-8"?>
    <Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
        <Relationship Id="rId99" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide" Target="slides/slide99.xml"/>
    </Relationships>"""
    (rels_dir / "presentation.xml.rels").write_text(rels_content, encoding="utf-8")

    pres_content = """<?xml version="1.0" encoding="UTF-8"?>
    <p:presentation xmlns:p="http://schemas.openxmlformats.org/presentationml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
        <p:sldIdLst>
            <p:sldId id="256" r:id="rId99"/>
        </p:sldIdLst>
    </p:presentation>"""
    (ppt_dir / "presentation.xml").write_text(pres_content, encoding="utf-8")

    with pytest.raises(RefusedToClean, match="None of the 1 slide.*match"):
        remove_orphaned_slides(tmp_path)

    assert slide1.exists()
