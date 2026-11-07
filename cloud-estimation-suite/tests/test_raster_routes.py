"""Consumer geometry measured independently from serialized SVG and PNG.

Compressed fractional lanes, wrong endpoint ports, missing route IDs, and
labels drawn over another route must fail these tests on the real renderer.
"""

from copy import deepcopy
from itertools import combinations
import json
from pathlib import Path
import re
from xml.etree import ElementTree as ET

from PIL import Image, ImageFont
import pytest

from tooling.diagram_renderer import render_diagram

NS = {"s": "http://www.w3.org/2000/svg"}
FIXTURE = Path(__file__).parent / "fixtures/provider-converging-flows.json"
FONT = Path(__file__).parents[1] / "tooling/fonts/lato/Lato-Regular.ttf"


def segments(path):
    values = list(map(float, re.findall(r"-?\d+(?:\.\d+)?", path.attrib["d"])))
    points = list(zip(values[::2], values[1::2]))
    assert len(points) >= 2
    return list(zip(points, points[1:]))


def parallel_span(first, second):
    (ax, ay), (bx, by) = first
    (cx, cy), (dx, dy) = second
    if ax == bx and cx == dx:
        return abs(ax - cx), min(max(ay, by), max(cy, dy)) - max(min(ay, by), min(cy, dy))
    if ay == by and cy == dy:
        return abs(ay - cy), min(max(ax, bx), max(cx, dx)) - max(min(ax, bx), min(cx, dx))
    return None


def rectangle(element):
    x, y, w, h = (float(element.attrib[key]) for key in ("x", "y", "width", "height"))
    return x, y, x + w, y + h


def segment_rectangle_distance(segment, rect):
    (ax, ay), (bx, by) = segment
    left, top, right, bottom = rect
    assert ax == bx or ay == by
    dx = max(left - max(ax, bx), min(ax, bx) - right, 0)
    dy = max(top - max(ay, by), min(ay, by) - bottom, 0)
    return (dx * dx + dy * dy) ** 0.5


def assert_raster_clearance(svg, graph):
    paths = {p.attrib["data-edge-id"]: p for p in svg.findall(".//s:path[@data-edge-id]", NS)}
    assert set(paths) == {e["id"] for e in graph["edges"]}
    measured = 0
    for first, second in combinations(paths.values(), 2):
        stroke = (float(first.attrib["stroke-width"]) + float(second.attrib["stroke-width"])) / 2
        for a in segments(first):
            for b in segments(second):
                relation = parallel_span(a, b)
                if relation and relation[1] > -3:
                    measured += 1
                    # Capsules also cover round/quantized ends where the
                    # parallel spans stop just short of one another.
                    distance = (relation[0] ** 2 + min(relation[1], 0) ** 2) ** 0.5
                    assert distance > stroke + 1, (first.attrib["data-edge-id"], second.attrib["data-edge-id"], relation)
                    rounded = parallel_span(tuple(tuple(round(v) for v in p) for p in a),
                                            tuple(tuple(round(v) for v in p) for p in b))
                    assert (rounded[0] ** 2 + min(rounded[1], 0) ** 2) ** 0.5 > stroke
    assert measured > 0
    nodes = {g.attrib["data-node-id"]: rectangle(g.find("s:rect", NS))
             for g in svg.findall(".//s:g[@data-node-id]", NS)}
    labels = svg.findall(".//s:rect[@data-edge-label-id]", NS)
    assert len(labels) == len(paths)
    tags = svg.findall(".//s:g[@data-flow-route-id]", NS)
    assert {g.attrib["data-flow-route-id"] for g in tags} == set(paths)
    boxes = [(None, rectangle(label)) for label in labels]
    boxes += [(g.attrib["data-flow-route-id"], rectangle(g.find("s:rect", NS))) for g in tags]
    font = ImageFont.truetype(str(FONT), 14, layout_engine=ImageFont.Layout.BASIC)
    # Group captions are text too: a vertical route between environments must
    # not strike a zone title just because it is outside the node rectangles.
    for group in svg.findall(".//s:g[@data-zone]", NS) + svg.findall(".//s:g[@data-environment]", NS):
        text = group.find("s:text", NS)
        x, baseline = float(text.attrib["x"]), float(text.attrib["y"])
        a, b, c, d = font.getbbox(text.text)
        boxes.append((None, (x + a, baseline - 14 + b, x + c, baseline - 14 + d)))
    for (_, a), (_, b) in combinations(boxes, 2):
        assert max(a[0], b[0]) >= min(a[2], b[2]) or max(a[1], b[1]) >= min(a[3], b[3])
    for owner, box in boxes:
        for node in nodes.values():
            assert max(box[0], node[0]) >= min(box[2], node[2]) or max(box[1], node[1]) >= min(box[3], node[3])
        for edge_id, path in paths.items():
            if edge_id != owner:
                assert all(segment_rectangle_distance(s, box) > 1 for s in segments(path)), (edge_id, owner, box)
    for g in tags:
        edge_id = g.attrib["data-flow-route-id"]
        assert edge_id in [t.text for t in g.findall("s:text", NS)]
        assert any(segment_rectangle_distance(s, rectangle(g.find("s:rect", NS))) == 0 for s in segments(paths[edge_id]))
    for edge in graph["edges"]:
        group = svg.find(f".//s:g[@data-flow-label='{edge['id']}']", NS)
        assert edge["label"] in [t.text for t in group.findall("s:text", NS)]
        assert edge["id"] in [t.text for t in group.findall("s:text", NS)]
    for edge_id, path in paths.items():
        for node_id, box in nodes.items():
            route = segments(path)
            for index, segment in enumerate(route):
                # Endpoint contacts belong to their own component; all other
                # capsules (radius 1 px) must stay clear of node rectangles.
                contact = ((index == 0 and node_id == path.attrib["data-source"])
                           or (index == len(route) - 1 and node_id == path.attrib["data-target"]))
                if not contact:
                    assert segment_rectangle_distance(segment, box) > 1


def graphs():
    provider = json.loads(FIXTURE.read_text(encoding="utf-8"))
    yield "provider", provider
    # Three single-node zones above one three-node zone used to offset
    # columns by 8 px, aliasing two otherwise distinct global route lanes.
    yield "staggered-zone-columns", {
        "nodes": [dict(id=str(i), component=f"Composant {i}", environment="A" if i < 3 else "B",
                       zone=str(i) if i < 3 else "Shared") for i in range(6)],
        "edges": [dict(id=str(i), source=a, target=b, label=f"Flux chiffré complet {i}")
                  for i, (a, b) in enumerate([("4", "0"), ("5", "4"), ("2", "0"), ("0", "0"),
                                              ("3", "2"), ("4", "1"), ("4", "5"), ("1", "2"),
                                              ("2", "5"), ("5", "5"), ("1", "2"), ("1", "1")])],
    }
    for topology in ("parallel", "self-loops", "chain", "many-flows", "all-directions", "mixed-zones"):
        graph = deepcopy(provider)
        if topology == "parallel":
            graph["edges"] = [{"id": f"F{i}", "source": "HTTP", "target": "DB", "label": f"Requête parallèle complète {i}"} for i in range(12)]
        elif topology == "self-loops":
            graph["edges"] += [{"id": f"LOOP{i}", "source": "HTTP", "target": "HTTP", "label": f"Boucle complète {i}"} for i in range(4)]
        elif topology == "chain":
            graph["edges"] = [{"id": f"CHAIN{i}", "source": a, "target": b, "label": f"Chaîne chiffrée complète {i}"}
                              for i, (a, b) in enumerate(zip(("HTTP", "DB", "BACKUP", "OBJ", "OBS"), ("DB", "BACKUP", "OBJ", "OBS", "EGRESS")))]
            for i, node in enumerate(graph["nodes"]):
                node.update(environment=f"Env {i % 2}", zone=f"Zone {i % 3}")
        elif topology == "many-flows":
            graph["edges"] = [{"id": f"M{i:02}", "source": "HTTP", "target": ["DB", "OBJ", "OBS", "EGRESS"][i % 4], "label": f"Flux multiple complet {i}"} for i in range(24)]
        else:
            graph["edges"] = [{"id": f"FLOW-DATABASE-REQUEST-{i:02}", "source": a["id"], "target": b["id"], "label": f"Requête chiffrée sans libellé tronqué {i}"}
                              for i, (a, b) in enumerate((a, b) for a in graph["nodes"] for b in graph["nodes"])]
            for i, node in enumerate(graph["nodes"]):
                if topology == "mixed-zones":
                    node.update(environment="A" if i < 3 else "B", zone=f"Zone {i}" if i < 3 else "Shared")
                else:
                    node.update(environment=f"Env {i % 2}", zone=f"Zone {i % 3}")
        yield topology, graph


@pytest.mark.parametrize("name,graph", list(graphs()), ids=lambda item: item if isinstance(item, str) else None)
def test_routes_remain_distinct_in_raster_with_traceable_ids(tmp_path, name, graph):
    render_diagram(graph, tmp_path / "a.svg", tmp_path / "a.png")
    assert_raster_clearance(ET.parse(tmp_path / "a.svg"), graph)
    with Image.open(tmp_path / "a.png") as image:
        assert image.format == "PNG" and image.getbbox()
    reordered = deepcopy(graph)
    reordered["nodes"].reverse()
    reordered["edges"].reverse()
    render_diagram(reordered, tmp_path / "b.svg", tmp_path / "b.png")
    assert (tmp_path / "a.svg").read_bytes() == (tmp_path / "b.svg").read_bytes()
    assert (tmp_path / "a.png").read_bytes() == (tmp_path / "b.png").read_bytes()
