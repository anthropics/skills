import importlib.util
from pathlib import Path

import pytest


SKILLS = Path(__file__).resolve().parents[2]
REL_NS = "http://schemas.openxmlformats.org/package/2006/relationships"


@pytest.mark.parametrize("skill", ["docx", "pptx", "xlsx"])
@pytest.mark.parametrize(
    ("target", "expected_valid"),
    [
        ("../../outside.txt", False),
        ("media.txt", True),
        ("My%20Image.txt", True),
    ],
)
def test_validator_keeps_relationships_inside_package(
    skill, target, expected_valid, tmp_path, monkeypatch, capsys
):
    office = SKILLS / skill / "scripts" / "office"
    monkeypatch.syspath_prepend(str(office))
    spec = importlib.util.spec_from_file_location(
        f"{skill}_validator_base", office / "validators" / "base.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    package = tmp_path / "package"
    document = package / "word" / "document.xml"
    document.parent.mkdir(parents=True)
    document.write_text("<document/>", encoding="utf-8")
    (tmp_path / "outside.txt").write_text("outside package", encoding="utf-8")
    if expected_valid:
        (document.parent / target.replace("%20", " ")).write_text(
            "inside package", encoding="utf-8"
        )

    root_rels = package / "_rels" / ".rels"
    root_rels.parent.mkdir()
    root_rels.write_text(
        f'<Relationships xmlns="{REL_NS}">'
        '<Relationship Id="rId1" Type="test" Target="word/document.xml"/>'
        '</Relationships>',
        encoding="utf-8",
    )
    document_rels = document.parent / "_rels" / "document.xml.rels"
    document_rels.parent.mkdir()
    document_rels.write_text(
        f'<Relationships xmlns="{REL_NS}">'
        f'<Relationship Id="rId1" Type="test" Target="{target}"/>'
        '</Relationships>',
        encoding="utf-8",
    )

    validator = module.BaseSchemaValidator(package)
    assert validator.validate_file_references() is expected_valid
    if not expected_valid:
        assert "outside.txt" in capsys.readouterr().out


@pytest.mark.parametrize("skill", ["docx", "pptx", "xlsx"])
@pytest.mark.parametrize("referenced", [False, True])
def test_validator_reports_outside_symlink_without_crashing(
    skill, referenced, tmp_path, monkeypatch, capsys
):
    office = SKILLS / skill / "scripts" / "office"
    monkeypatch.syspath_prepend(str(office))
    spec = importlib.util.spec_from_file_location(
        f"{skill}_validator_base_symlink", office / "validators" / "base.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    package = tmp_path / "package"
    document = package / "word" / "document.xml"
    document.parent.mkdir(parents=True)
    document.write_text("<document/>", encoding="utf-8")
    outside = tmp_path / "outside.bin"
    outside.write_bytes(b"outside package")
    link = document.parent / "link.bin"
    try:
        link.symlink_to(outside)
    except OSError as exc:
        pytest.skip(f"symlinks unavailable: {exc}")

    root_rels = package / "_rels" / ".rels"
    root_rels.parent.mkdir()
    root_rels.write_text(
        f'<Relationships xmlns="{REL_NS}">'
        '<Relationship Id="rId1" Type="test" Target="word/document.xml"/>'
        '</Relationships>',
        encoding="utf-8",
    )
    if referenced:
        document_rels = document.parent / "_rels" / "document.xml.rels"
        document_rels.parent.mkdir()
        document_rels.write_text(
            f'<Relationships xmlns="{REL_NS}">'
            '<Relationship Id="rId1" Type="test" Target="link.bin"/>'
            '</Relationships>',
            encoding="utf-8",
        )

    validator = module.BaseSchemaValidator(package)
    assert validator.validate_file_references() is False
    output = capsys.readouterr().out
    assert "link.bin" in output
    assert "outside package" in output
