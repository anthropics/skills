from __future__ import annotations

import hashlib
import importlib
import shutil
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))
keynote = importlib.import_module("office.helpers.keynote")


PRESENTATION = f'''<?xml version="1.0" encoding="UTF-8"?>
<p:presentation xmlns:p="{keynote.PRESENTATION_NS}" xmlns:r="{keynote.OFFICE_REL_NS}">
  <p:sldMasterIdLst><p:sldMasterId id="1" r:id="rId1"/></p:sldMasterIdLst>
  <p:sldIdLst><p:sldId id="256" r:id="rId7"/></p:sldIdLst>
  <p:sldSz cx="12191695" cy="6858000" type="screen4x3"/>
  <p:notesSz cx="6858000" cy="9144000"/>
</p:presentation>'''

RELS = """<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId8" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/notesMaster" Target="notesMasters/notesMaster1.xml"/>
  <Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/printerSettings" Target="printerSettings/printerSettings1.bin"/>
</Relationships>"""

CONTENT_TYPES = f'''<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="xml" ContentType="application/xml"/>
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
  <Default Extension="bin" ContentType="{keynote.PRINTER_SETTINGS_CONTENT_TYPE}"/>
  <Override PartName="/ppt/presentation.xml" ContentType="application/vnd.openxmlformats-officedocument.presentationml.presentation.main+xml"/>
</Types>'''


def package(**extra: bytes) -> dict[str, bytes]:
    files = {
        keynote.PRESENTATION: PRESENTATION.encode(),
        keynote.PRESENTATION_RELS: RELS.encode(),
        keynote.CONTENT_TYPES: CONTENT_TYPES.encode(),
        "ppt/printerSettings/printerSettings1.bin": b"printer",
    }
    files.update(extra)
    return files


def write_package(path: Path, files: dict[str, bytes]) -> None:
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
        for name, data in files.items():
            archive.writestr(name, data)


class KeynoteSanitizerTests(unittest.TestCase):
    def test_widescreen_is_canonicalized(self):
        xml, changed = keynote._patch_slide_size(PRESENTATION)
        self.assertTrue(changed)
        self.assertIn('cx="12192000" cy="6858000"', xml)
        self.assertNotIn('type="screen4x3"', xml)

    def test_standard_4x3_is_preserved(self):
        source = PRESENTATION.replace("12191695", "9143990")
        xml, changed = keynote._patch_slide_size(source)
        self.assertTrue(changed)
        self.assertIn('cx="9144000" cy="6858000" type="screen4x3"', xml)

    def test_custom_size_only_loses_contradictory_type(self):
        source = PRESENTATION.replace("12191695", "10000000").replace(
            "6858000", "7000000"
        )
        xml, changed = keynote._patch_slide_size(source)
        self.assertTrue(changed)
        self.assertIn('cx="10000000" cy="7000000"', xml)
        self.assertNotIn('type="screen4x3"', xml)

    def test_malformed_slide_size_is_left_unchanged(self):
        source = PRESENTATION.replace(' cx="12191695"', "")
        xml, changed = keynote._patch_slide_size(source)
        self.assertFalse(changed)
        self.assertEqual(source, xml)

    def test_notes_master_is_inserted_before_slide_list(self):
        xml, changed = keynote._add_notes_master_id(PRESENTATION, RELS)
        self.assertTrue(changed)
        self.assertLess(xml.index("notesMasterIdLst"), xml.index("sldIdLst"))
        self.assertIn('r:id="rId8"', xml)

    def test_existing_notes_master_is_not_reordered(self):
        existing = PRESENTATION.replace(
            "</p:sldIdLst>",
            '</p:sldIdLst><p:notesMasterIdLst><p:notesMasterId r:id="rId8"/></p:notesMasterIdLst>',
        )
        xml, changed = keynote._add_notes_master_id(existing, RELS)
        self.assertFalse(changed)
        self.assertEqual(existing, xml)

    def test_no_notes_relationship_is_a_noop(self):
        rels = RELS.replace(
            '<Relationship Id="rId8" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/notesMaster" Target="notesMasters/notesMaster1.xml"/>',
            "",
        )
        xml, changed = keynote._add_notes_master_id(PRESENTATION, rels)
        self.assertFalse(changed)
        self.assertEqual(PRESENTATION, xml)

    def test_printer_settings_are_removed(self):
        repaired, changes = keynote.sanitize_entries(package())
        self.assertNotIn("ppt/printerSettings/printerSettings1.bin", repaired)
        self.assertNotIn(b"printerSettings", repaired[keynote.PRESENTATION_RELS])
        self.assertNotIn(
            keynote.PRINTER_SETTINGS_CONTENT_TYPE.encode(),
            repaired[keynote.CONTENT_TYPES],
        )
        self.assertIn("removed Windows printer settings safely", changes)

    def test_existing_ole_override_survives(self):
        content_types = CONTENT_TYPES.replace(
            "</Types>",
            f'<Override PartName="/ppt/embeddings/oleObject1.bin" ContentType="{keynote.OLE_OBJECT_CONTENT_TYPE}"/></Types>',
        )
        files = package(
            **{
                keynote.CONTENT_TYPES: content_types.encode(),
                "ppt/embeddings/oleObject1.bin": b"ole",
            }
        )
        repaired, _ = keynote.sanitize_entries(files)
        self.assertIn("ppt/embeddings/oleObject1.bin", repaired)
        self.assertIn(
            keynote.OLE_OBJECT_CONTENT_TYPE.encode(), repaired[keynote.CONTENT_TYPES]
        )

    def test_ole_relationship_gets_specific_override(self):
        slide_rels = b"""<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId3" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/oleObject" Target="../embeddings/OleObject1.bin"/></Relationships>"""
        files = package(
            **{
                "ppt/embeddings/OleObject1.bin": b"ole",
                "ppt/slides/_rels/slide1.xml.rels": slide_rels,
            }
        )
        repaired, _ = keynote.sanitize_entries(files)
        content_types = repaired[keynote.CONTENT_TYPES]
        self.assertIn(b"/ppt/embeddings/OleObject1.bin", content_types)
        self.assertIn(keynote.OLE_OBJECT_CONTENT_TYPE.encode(), content_types)

    def test_unknown_bin_part_is_rejected(self):
        with self.assertRaisesRegex(keynote.SanitizeError, "no specific content type"):
            keynote.sanitize_entries(package(**{"ppt/embeddings/unknown.bin": b"?"}))

    def test_file_sanitization_is_idempotent(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "deck.pptx"
            write_package(path, package())
            first_changes = keynote.sanitize_file(path)
            first_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            second_changes = keynote.sanitize_file(path)
            second_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertTrue(first_changes)
            self.assertEqual([], second_changes)
            self.assertEqual(first_hash, second_hash)

    def test_atomic_write_failure_preserves_original(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "deck.pptx"
            write_package(path, package())
            backup = Path(temp_dir) / "original.pptx"
            shutil.copy2(path, backup)
            original_writestr = zipfile.ZipFile.writestr
            calls = 0

            def fail_on_second_write(archive, *args, **kwargs):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise OSError("simulated write failure")
                return original_writestr(archive, *args, **kwargs)

            with (
                mock.patch.object(zipfile.ZipFile, "writestr", fail_on_second_write),
                self.assertRaisesRegex(OSError, "simulated write failure"),
            ):
                keynote.sanitize_file(path)
            self.assertEqual(backup.read_bytes(), path.read_bytes())


if __name__ == "__main__":
    unittest.main()
