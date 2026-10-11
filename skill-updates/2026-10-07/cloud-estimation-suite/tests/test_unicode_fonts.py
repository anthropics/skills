"""Real raster glyphs, byte-preserving font delivery and bounded licence scanning."""

from hashlib import sha256
import json
from pathlib import Path
import site
import subprocess
import sys
from xml.etree import ElementTree as ET
from zipfile import ZipFile

from PIL import Image
import pytest

from tooling.anonymisation import _load_policy, _Scanner, scan_tree
from tooling.diagram_renderer import render_diagram
from tooling import sync_shared
from tooling import diagram_renderer

ROOT = Path(__file__).parents[1]
NS = {"s": "http://www.w3.org/2000/svg"}
LICENSE_PATH = "tooling/fonts/lato/OFL.txt"
SKILLS = [record["name"] for record in json.loads((ROOT / "tooling/domain-registry.json").read_bytes())["skills"]]


def raster_glyph(directory, value):
    graph = {"nodes": [{"id": "GLYPH", "component": value}], "edges": []}
    render_diagram(graph, directory / "glyph.svg", directory / "glyph.png")
    node = ET.parse(directory / "glyph.svg").find('.//s:g[@data-node-id]/s:rect', NS)
    x, y = int(node.attrib["x"]), int(node.attrib["y"])
    with Image.open(directory / "glyph.png") as image:
        return image.crop((x + 12, y + 12, x + 60, y + 40)).tobytes()


@pytest.mark.parametrize("accent,plain", [("é", "e"), ("è", "e"), ("ê", "e"),
    ("à", "a"), ("ç", "c"), ("œ", "oe"), ("É", "E"), ("ù", "u"), ("î", "i")])
def test_rendered_accent_is_distinct_from_missing_glyph_and_ascii(tmp_path, accent, plain):
    accent_pixels = raster_glyph(tmp_path / "accent", accent)
    assert accent_pixels != raster_glyph(tmp_path / "missing", "\u0378")
    assert accent_pixels != raster_glyph(tmp_path / "plain", plain)


def test_sync_preserves_font_binary_bytes_including_cr(tmp_path, monkeypatch):
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    raw = b"\x00\x01\x00\x00binary\r\nfont\rtable\xff"
    (canonical / "font.ttf").write_bytes(raw)
    skill = tmp_path / "skill"
    skill.mkdir()
    (skill / "SKILL.md").write_bytes(b"Synthetic skill\n")
    monkeypatch.setattr(sync_shared, "CANONICAL", canonical)
    monkeypatch.setattr(sync_shared, "SHARED", {"scripts/fonts/lato/font.ttf": "font.ttf"})
    sync_shared.sync_skill(skill)
    assert (skill / "scripts/fonts/lato/font.ttf").read_bytes() == raw
    manifest = json.loads((skill / "manifest.json").read_bytes())
    assert manifest["files"]["scripts/fonts/lato/font.ttf"] == sha256(raw).hexdigest()


def test_exact_distributed_license_is_public_but_still_scans_private_terms(tmp_path):
    destination = tmp_path / LICENSE_PATH
    destination.parent.mkdir(parents=True)
    destination.write_bytes((ROOT / LICENSE_PATH).read_bytes())
    assert scan_tree(tmp_path).clean
    policy = _load_policy(None)
    policy["denylist"] = ["Lato"]
    scanner = _Scanner(policy)
    scanner.text(destination.read_bytes(), LICENSE_PATH, True)
    assert any(match.rule == "denylist-token" for match in scanner.report.matches)


@pytest.mark.parametrize("defect", ["wrong-path", "changed-hash"])
def test_license_public_identity_exemption_is_exact_path_and_hash(tmp_path, defect):
    path = tmp_path / (LICENSE_PATH if defect == "changed-hash" else "copied.txt")
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = (ROOT / LICENSE_PATH).read_bytes()
    path.write_bytes(raw + (b"\nModified copy\n" if defect == "changed-hash" else b""))
    report = scan_tree(tmp_path)
    assert not report.clean and any(match.rule == "email" for match in report.matches)


def test_french_labels_remain_complete_and_svg_declares_font_family(tmp_path):
    graph = {"nodes": [
        {"id": "HTTP", "component": "Entrée HTTP", "zone": "Périmètre logique proposé"},
        {"id": "OBS", "component": "Observabilité", "zone": "Périmètre logique proposé"}],
        "edges": [{"id": "F-01", "source": "HTTP", "target": "OBS", "label": "Télémétrie : proposée"}]}
    render_diagram(graph, tmp_path / "french.svg", tmp_path / "french.png")
    root = ET.parse(tmp_path / "french.svg")
    texts = root.findall(".//s:text", NS)
    assert {element.text for element in texts} >= {"Entrée HTTP", "Périmètre logique proposé", "Télémétrie : proposée"}
    assert all(element.attrib["font-family"] == "Lato, sans-serif" for element in texts)


def test_changed_font_hash_is_refused_before_outputs(tmp_path, monkeypatch):
    raw = bytearray((ROOT / "tooling/fonts/lato/Lato-Regular.ttf").read_bytes())
    raw[-1] ^= 1
    altered = tmp_path / "altered.ttf"
    altered.write_bytes(raw)
    monkeypatch.setattr(diagram_renderer, "FONT_PATH", altered)
    with pytest.raises(ValueError, match="font checksum"):
        render_diagram({"nodes": [{"id": "APP"}]}, tmp_path / "refused.svg", tmp_path / "refused.png")
    assert not (tmp_path / "refused.svg").exists()
    assert not (tmp_path / "refused.png").exists()


@pytest.mark.parametrize("name", SKILLS)
def test_extracted_bundle_contains_exact_font_license_and_renders_without_suite(name, tmp_path):
    with ZipFile(ROOT / "bundles" / (name + ".skill")) as archive:
        for filename in ("Lato-Regular.ttf", "OFL.txt", "provenance.json"):
            assert archive.read(name + "/scripts/fonts/lato/" + filename) == (ROOT / "tooling/fonts/lato" / filename).read_bytes()
        archive.extractall(tmp_path)
    program = """
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path.cwd()))
sys.path.extend(json.loads(sys.argv[1]))
from scripts.diagram_renderer import render_diagram
from PIL import Image
from xml.etree import ElementTree as ET
ns = {'s': 'http://www.w3.org/2000/svg'}
def crop(value, name):
    render_diagram({'nodes': [{'id': 'GLYPH', 'component': value}]}, Path(name + '.svg'), Path(name + '.png'))
    node = ET.parse(name + '.svg').find('.//s:g[@data-node-id]/s:rect', ns)
    x, y = int(node.attrib['x']), int(node.attrib['y'])
    with getattr(Image, 'open')(name + '.png') as png:
        return getattr(png, 'crop')((x + 12, y + 12, x + 60, y + 40)).tobytes()
assert Path(sys.modules['scripts.diagram_renderer'].__file__).resolve().is_relative_to(Path.cwd())
accent = crop(chr(233), 'accent')
assert accent != crop(chr(0x378), 'missing')
assert accent != crop('e', 'plain')
print('isolated-bundle-unicode=verified')
"""
    dependencies = [*site.getsitepackages(), site.getusersitepackages()]
    result = subprocess.run([sys.executable, "-I", "-c", program, json.dumps(dependencies)],
                            cwd=tmp_path / name, text=True, capture_output=True, timeout=45)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "isolated-bundle-unicode=verified"
