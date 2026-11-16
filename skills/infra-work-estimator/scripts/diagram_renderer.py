"""Deterministic, self-contained SVG/PNG architecture diagrams.

Nodes require ``id`` and accept component/label, environment, zone, provider,
and icon (a manifest-relative PNG path). Edges require id/source/target and
accept label. No connections are inferred. Local icon packs are all-or-nothing:
each asset needs a verified hash and an official source with a usage notice.
Only PNG assets are supported; unsupported packs safely use neutral symbols.
Byte determinism is within the same Python/Pillow version and rendering fonts.
"""

import base64
from dataclasses import asdict, dataclass
from hashlib import sha256
import heapq
from io import BytesIO
import json
import math
from pathlib import Path
import re
import textwrap
from xml.etree import ElementTree as ET

from PIL import Image, ImageDraw, ImageFont

POLICY = json.loads(Path(__file__).with_name("icon-policy.json").read_text(encoding="utf-8"))
FONT_PATH = Path(__file__).with_name("fonts") / "lato" / "Lato-Regular.ttf"
FONT_SHA256 = "d636e4683231f931eda222d588e944d082bfd3bdba02f928bee461c0f185b251"
NODE_W, NODE_H = 240, 112
LANE_PITCH = 8  # 2 px stroke diameter + rounding reserve, with visible whitespace.
PORT_PITCH = 32  # Leaves room for a complete 20 px route-ID badge.


@dataclass
class DiagramManifest:
    node_ids: list[str]
    edge_ids: list[str]
    icon_sources: list[str]
    icon_provenance: list[dict]
    output_hashes: dict[str, str]
    warnings: list[str]

    def to_dict(self) -> dict:
        """Public provenance contains relative asset names, never local paths."""
        return asdict(self)


def _text(value, location, *, required=False):
    if not isinstance(value, str) or (required and not value.strip()):
        raise ValueError(f"{location}: expected {'non-empty ' if required else ''}text")
    if any((ord(char) < 32 and char not in "\t\n\r") or 0xD800 <= ord(char) <= 0xDFFF
           or ord(char) in (0xFFFE, 0xFFFF) for char in value):
        raise ValueError(f"{location}: invalid XML text")
    return value


def _graph(architecture):
    if not isinstance(architecture, dict) or not isinstance(architecture.get("nodes"), list) or not isinstance(architecture.get("edges", []), list):
        raise ValueError("architecture: expected nodes and edges lists")
    nodes, edges = [], []
    for row in architecture["nodes"]:
        if not isinstance(row, dict):
            raise ValueError("node: expected an object")
        node = {"id": _text(row.get("id"), "node.id", required=True)}
        for key, default in (("component", row.get("label", node["id"])), ("environment", "Unspecified"), ("zone", "Unspecified"), ("provider", ""), ("icon", "")):
            node[key] = _text(row.get(key, default), f"node.{key}")
        nodes.append(node)
    ids = [node["id"] for node in nodes]
    if len(ids) != len(set(ids)):
        raise ValueError("architecture: duplicate node ID")
    for row in architecture.get("edges", []):
        if not isinstance(row, dict):
            raise ValueError("edge: expected an object")
        edge = {key: _text(row.get(key), f"edge.{key}", required=True) for key in ("id", "source", "target")}
        edge["label"] = _text(row.get("label", ""), "edge.label")
        if edge["source"] not in ids or edge["target"] not in ids:
            raise ValueError(f"edge {edge['id']}: unknown node")
        edges.append(edge)
    if len(edges) != len({edge["id"] for edge in edges}):
        raise ValueError("architecture: duplicate edge ID")
    return sorted(nodes, key=lambda node: node["id"]), sorted(edges, key=lambda edge: edge["id"])


def _icon_pack(pack):
    if pack is None:
        return {}, []
    try:
        pack = Path(pack).resolve(strict=True)
        manifest = json.loads((pack / "manifest.json").read_text(encoding="utf-8"))
        provider = _text(manifest["provider"], "icon.provider", required=True)
        source = _text(manifest["official_source_url"], "icon.official_source_url", required=True)
        if source not in POLICY["official_sources"].get(provider, []):
            raise ValueError("unofficial source")
        notices = [_text(manifest[key], f"icon.{key}", required=True)
                   for key in POLICY["manifest"]["notice_one_of"] if key in manifest]
        notice = next(iter(notices), None)
        if notice is None or not isinstance(manifest["assets"], list) or not manifest["assets"]:
            raise ValueError("incomplete manifest")
        assets = {}
        listed = set()
        for entry in manifest["assets"]:
            relative = _text(entry["path"], "icon.path", required=True)
            digest = _text(entry["sha256"], "icon.sha256", required=True)
            if not isinstance(relative, str) or "\\" in relative or not isinstance(digest, str) or not re.fullmatch("[0-9a-fA-F]{64}", digest):
                raise ValueError("invalid asset record")
            parts = relative.split("/")
            if any(part in ("", ".", "..") for part in parts) or Path(relative).is_absolute() or ":" in relative:
                raise ValueError("asset traversal")
            path = (pack / relative).resolve(strict=True)
            if not path.is_relative_to(pack) or path in listed or path.suffix.lower() != ".png":
                raise ValueError("unsupported or duplicate asset")
            listed.add(path)
            if path.stat().st_size > POLICY["max_asset_bytes"]:
                raise ValueError("oversize asset")
            content = path.read_bytes()
            if sha256(content).hexdigest() != digest.lower():
                raise ValueError("asset checksum")
            with Image.open(BytesIO(content)) as image:
                if image.format != "PNG" or max(image.size) > POLICY["max_asset_dimension"]:
                    raise ValueError("unsupported image")
                image.verify()
            provenance = {"path": relative, "sha256": digest.lower(), "provider": provider,
                          "official_source_url": source, "licence_or_trademark_notice": notice}
            assets[relative] = (content, provenance)
        actual = {path.resolve() for path in pack.rglob("*") if path.is_file() and path != pack / "manifest.json"}
        if actual != listed:
            raise ValueError("unlisted asset")
        return assets, []
    except (OSError, ValueError, KeyError, TypeError, StopIteration, Image.DecompressionBombError):
        return {}, ["Unverified icon pack; provider-neutral symbols used."]


def _layout(nodes, clearance=20, node_height=NODE_H):
    """Environment bands containing zone groups; IDs sort inside each group."""
    groups, positions = [], {}
    y, width = 40, 360
    margin = max(20, clearance + 12)
    column_gap = 2 * margin + 16
    row_gap = max(48, 2 * clearance + 24)
    for environment in sorted({node["environment"] for node in nodes}):
        zones = sorted({node["zone"] for node in nodes if node["environment"] == environment})
        x, band_height = 40, 0
        for zone in zones:
            members = [node for node in nodes if node["environment"] == environment and node["zone"] == zone]
            columns = min(3, len(members))
            zone_width = columns * NODE_W + (columns - 1) * column_gap + 2 * margin
            zone_height = math.ceil(len(members) / columns) * (node_height + row_gap) + 80
            groups.append(("zone", zone, x, y + 36, zone_width, zone_height))
            for index, node in enumerate(members):
                positions[node["id"]] = (x + margin + index % columns * (NODE_W + column_gap),
                                         y + 104 + clearance + index // columns * (node_height + row_gap))
            # A zone boundary consumes the same pitch as a column boundary.
            # Otherwise differently grouped environment bands shift columns
            # into another edge's lane even when each local gap is ample.
            x += zone_width + column_gap - 2 * margin
            band_height = max(band_height, zone_height + 56)
        groups.append(("environment", environment, 20, y, x, band_height))
        width = max(width, x + 40)
        y += band_height + 24
    return groups, positions, width, max(180, y + 20)


def _clear_segment(first, second, obstacles):
    """Rectilinear segments cannot enter any padded node rectangle."""
    ax, ay = first
    bx, by = second
    for left, top, right, bottom in obstacles:
        if ax == bx:
            if left < ax < right and max(min(ay, by), top) < min(max(ay, by), bottom):
                return False
        elif top < ay < bottom and max(min(ax, bx), left) < min(max(ax, bx), right):
            return False
    return True


def _route(source, target, positions, lane=0, *, node_height=NODE_H, stub=16, text_boxes=()):
    """Shortest deterministic rectilinear route avoiding every node, plus stubs.

    The visibility grid uses the gaps around all rectangles. Dijkstra state
    includes direction so a small bend penalty favours readable routes. Fixed
    coordinate ordering resolves equal-cost paths without input-order effects.
    """
    x, y = source
    tx, ty = target
    # Do not compress lanes into a fixed gap: every sorted edge owns an integer
    # grid offset and port. Layout grows to contain this footprint. The initial
    # stub carries the full ID; all middle segments avoid every badge and group
    # caption as well as every component. A loop uses a separate return port.
    offset = stub + LANE_PITCH * lane
    gap = LANE_PITCH * (lane + 1)
    port = 24 + PORT_PITCH * lane
    return_port = port + (16 if source == target else 0)
    obstacles = [(nx - 4, ny - 4, nx + NODE_W + 4, ny + node_height + 4) for nx, ny in positions.values()]
    obstacles += [(a - 2, b - 2, c + 2, d + 2) for a, b, c, d in text_boxes]
    start, end = (x + NODE_W + offset, y + port), (tx + NODE_W + offset, ty + return_port)
    xs = sorted({coordinate for nx, _ in positions.values() for coordinate in (nx - offset, nx + NODE_W + offset)})
    ys = sorted({start[1], end[1]} | {coordinate for _, ny in positions.values() for coordinate in (ny - gap, ny + node_height + gap)})
    xi, yi = {value: index for index, value in enumerate(xs)}, {value: index for index, value in enumerate(ys)}
    initial = (start, 1)  # Initial stub is horizontal.
    queue, costs, previous = [(0, start, 1)], {initial: 0}, {}
    final = None
    while queue:
        cost, point, direction = heapq.heappop(queue)
        state = (point, direction)
        if cost != costs[state]:
            continue
        if point == end:
            final = state
            break
        px, py = point
        ix, iy = xi[px], yi[py]
        neighbours = []
        for offset in (-1, 1):
            if 0 <= ix + offset < len(xs):
                neighbours.append(((xs[ix + offset], py), 1))
            if 0 <= iy + offset < len(ys):
                neighbours.append(((px, ys[iy + offset]), 2))
        for next_point, next_direction in sorted(neighbours):
            nx, ny = next_point
            if any(left <= nx <= right and top <= ny <= bottom for left, top, right, bottom in obstacles):
                continue
            if not _clear_segment(point, next_point, obstacles):
                continue
            candidate = cost + abs(nx - px) + abs(ny - py) + (18 if direction != next_direction else 0)
            next_state = (next_point, next_direction)
            if candidate < costs.get(next_state, math.inf):
                costs[next_state], previous[next_state] = candidate, state
                heapq.heappush(queue, (candidate, next_point, next_direction))
    if final is None:
        raise ValueError("diagram: no unobstructed route between nodes")
    middle = []
    while final != initial:
        middle.append(final[0])
        final = previous[final]
    points = [(x + NODE_W, start[1]), start] + list(reversed(middle)) + [(tx + NODE_W, end[1])]
    simplified = []
    for point in points:
        if len(simplified) >= 2:
            ax, ay = simplified[-2]
            bx, by = simplified[-1]
            if ax == bx == point[0] or ay == by == point[1]:
                simplified.pop()
        simplified.append(point)
    return simplified


def render_diagram(architecture: dict, svg: Path, png: Path, icon_pack: Path | None = None) -> DiagramManifest:
    """Render complete inventory IDs and explicit directed flows without network I/O."""
    nodes, edges = _graph(architecture)
    for edge in edges:
        # SVG whitespace and Pillow newlines must describe the same measured label.
        edge["label"] = " ".join((edge["label"].strip() or edge["id"]).split())
    svg, png = Path(svg), Path(png)
    if svg.resolve() == png.resolve():
        raise ValueError("SVG and PNG output paths must differ")
    assets, warnings = _icon_pack(icon_pack)
    used = {}
    for node in nodes:
        asset = assets.get(node["icon"])
        if asset and node["provider"] == asset[1]["provider"]:
            used[node["id"]] = asset
    font_bytes = FONT_PATH.read_bytes()
    if sha256(font_bytes).hexdigest() != FONT_SHA256:
        raise ValueError("diagram: bundled Lato font checksum mismatch")
    font = ImageFont.truetype(BytesIO(font_bytes), size=14, layout_engine=ImageFont.Layout.BASIC)
    display_ids = {edge["id"]: " ".join(edge["id"].split()) for edge in edges}
    id_widths = {key: math.ceil(font.getlength(value)) + 12 for key, value in display_ids.items()}
    stub = max(id_widths.values(), default=0) + 16
    clearance = max(20, stub + LANE_PITCH * len(edges))
    node_height = max(NODE_H, 48 + PORT_PITCH * len(edges))
    groups, positions, width, height = _layout(nodes, clearance, node_height)
    heading_boxes = []
    for _, value, x, y, _, _ in groups:
        left, top, right, bottom = font.getbbox(value)
        heading_boxes.append((x + 12 + left, y + 8 + top, x + 12 + right, y + 8 + bottom))
    route_badges = {}
    for index, edge in enumerate(edges):
        x, y = positions[edge["source"]]
        left, top = x + NODE_W + 4, y + 24 + PORT_PITCH * index - 10
        route_badges[edge["id"]] = (left, top, left + id_widths[edge["id"]], top + 20)
    routes = {edge["id"]: _route(positions[edge["source"]], positions[edge["target"]], positions, index,
                                node_height=node_height, stub=stub,
                                text_boxes=[*route_badges.values(), *heading_boxes])
              for index, edge in enumerate(edges)}
    # Measure full labels; do not disguise collisions by truncating their text.
    label_boxes = {}
    occupied = [(x - 4, y - 4, x + NODE_W + 4, y + node_height + 4) for x, y in positions.values()]
    occupied += [*route_badges.values(), *heading_boxes]
    all_segments = [pair for points in routes.values() for pair in zip(points, points[1:])]
    footer = height
    for edge in edges:
        value = edge["label"] or edge["id"]
        bounds = font.getbbox(value)
        w, h = max(bounds[2] - bounds[0], math.ceil(len(value) * 9)) + id_widths[edge["id"]] + 20, 28
        points = routes[edge["id"]]
        candidates = []
        for first, second in sorted(zip(points, points[1:]), key=lambda p: -(abs(p[1][0] - p[0][0]) + abs(p[1][1] - p[0][1]))):
            if first[1] == second[1]:
                candidates.extend([((first[0] + second[0] - w) / 2, first[1] - h - 4),
                                   ((first[0] + second[0] - w) / 2, first[1] + 4)])
        box = None
        for lx, ly in candidates:
            rect = (lx, ly, lx + w, ly + h)
            if lx < 4 or ly < 4 or lx + w > width - 4 or ly + h > height - 4:
                continue
            if any(max(lx, a) < min(lx + w, c) and max(ly, b) < min(ly + h, d) for a, b, c, d in occupied):
                continue
            if any(not _clear_segment(a, b, [(lx - 2, ly - 2, lx + w + 2, ly + h + 2)]) for a, b in all_segments):
                continue
            box = rect
            break
        if box is None:
            # Dedicated numbered flow legend, outside node/route occupancy.
            box = (24, footer + 8, 24 + w, footer + 8 + h)
            footer += h + 12
            width = max(width, math.ceil(box[2] + 24))
        occupied.append(box)
        label_boxes[edge["id"]] = box
    height = max(height, math.ceil(footer + (20 if footer != height else 0)))
    root = ET.Element("svg", {"xmlns": "http://www.w3.org/2000/svg", "width": str(width), "height": str(height), "viewBox": f"0 0 {width} {height}"})
    ET.SubElement(root, "title").text = "Architecture diagram"
    provenance = sorted({asset[1]["path"]: asset[1] for asset in used.values()}.values(), key=lambda item: item["path"])
    sources = (["provider-neutral"] if len(used) < len(nodes) or not nodes else []) + sorted({item["official_source_url"] for item in provenance})
    ET.SubElement(root, "metadata").text = json.dumps({"icon_sources": sources, "icon_provenance": provenance}, sort_keys=True, ensure_ascii=False)
    definitions = ET.SubElement(root, "defs")
    marker = ET.SubElement(definitions, "marker", {"id": "arrow", "viewBox": "0 0 10 10", "refX": "9", "refY": "5", "markerWidth": "7", "markerHeight": "7", "orient": "auto-start-reverse"})
    ET.SubElement(marker, "path", {"d": "M 0 0 L 10 5 L 0 10 z", "fill": "#345678"})
    canvas = Image.new("RGB", (width, height), "white")
    draw = ImageDraw.Draw(canvas)

    def rectangle(parent, x, y, w, h, fill, stroke):
        ET.SubElement(parent, "rect", {"x": str(x), "y": str(y), "width": str(w), "height": str(h), "rx": "6", "fill": fill, "stroke": stroke})
        draw.rounded_rectangle((x, y, x + w, y + h), radius=6, fill=fill, outline=stroke)

    def text(parent, x, y, value, colour="#17365d"):
        ET.SubElement(parent, "text", {"x": str(x), "y": str(y + 14), "font-family": "Lato, sans-serif", "font-size": "14", "fill": colour}).text = value
        draw.text((x, y), value, font=font, fill=colour)

    for kind in ("environment", "zone"):
        for group_kind, label, x, y, w, h in groups:
            if group_kind == kind:
                group = ET.SubElement(root, "g", {f"data-{kind}": label})
                rectangle(group, x, y, w, h, "#f2f6fa" if kind == "environment" else "#ffffff", "#c3d1df")
                text(group, x + 12, y + 8, label)
    for edge in edges:
        points = routes[edge["id"]]
        path = "M " + " L ".join(f"{x:g} {y:g}" for x, y in points)
        ET.SubElement(root, "path", {"data-edge-id": edge["id"], "data-source": edge["source"], "data-target": edge["target"], "d": path, "stroke": "#345678", "stroke-width": "2", "fill": "none", "marker-end": "url(#arrow)"})
        draw.line(points, fill="#345678", width=2)
        (ax, ay), (bx, by) = points[-2:]
        angle = math.atan2(by - ay, bx - ax)
        draw.polygon([(bx, by), (bx - 10 * math.cos(angle - 0.4), by - 10 * math.sin(angle - 0.4)), (bx - 10 * math.cos(angle + 0.4), by - 10 * math.sin(angle + 0.4))], fill="#345678")
    for node in nodes:
        x, y = positions[node["id"]]
        group = ET.SubElement(root, "g", {"data-node-id": node["id"]})
        ET.SubElement(group, "title").text = f"{node['id']}: {node['component']}"
        rectangle(group, x, y, NODE_W, node_height, "#e7f0f8", "#345678")
        offset = 12
        if node["id"] in used:
            content = used[node["id"]][0]
            ET.SubElement(group, "image", {"x": str(x + 12), "y": str(y + 14), "width": "40", "height": "40", "href": "data:image/png;base64," + base64.b64encode(content).decode("ascii")})
            with Image.open(BytesIO(content)) as original:
                icon = original.convert("RGBA")
                icon.thumbnail((40, 40), Image.Resampling.LANCZOS)
                canvas.paste(icon, (x + 12, y + 14), icon)
            offset = 62
        for index, line in enumerate(textwrap.wrap(node["component"], width=22 if offset > 12 else 29)[:3]):
            text(group, x + offset, y + 12 + index * 18, line)
        text(group, x + 12, y + node_height - 28, node["id"])
    for edge in edges:
        x, y, right, bottom = route_badges[edge["id"]]
        group = ET.SubElement(root, "g", {"data-flow-route-id": edge["id"]})
        ET.SubElement(group, "title").text = f"{edge['id']}: {edge['source']} -> {edge['target']}"
        rectangle(group, x, y, right - x, bottom - y, "#ffffff", "#345678")
        text(group, x + 4, y + 2, display_ids[edge["id"]])
    for edge in edges:
        x, y, right, bottom = label_boxes[edge["id"]]
        label_group = ET.SubElement(root, "g", {"data-flow-label": edge["id"]})
        ET.SubElement(label_group, "title").text = f"{edge['id']}: {edge['source']} -> {edge['target']}"
        rectangle(label_group, x, y, right - x, bottom - y, "#ffffff", "#b8c8d8")
        label_group[-1].set("data-edge-label-id", edge["id"])
        text(label_group, x + 4, y + 4, edge["label"] or display_ids[edge["id"]])
        text(label_group, right - id_widths[edge["id"]], y + 4, display_ids[edge["id"]])
    if not nodes:
        text(root, 24, 40, "No inventory nodes supplied")
    svg_bytes = ET.tostring(root, encoding="utf-8")
    buffer = BytesIO()
    canvas.save(buffer, format="PNG", optimize=False, compress_level=9)
    png_bytes = buffer.getvalue()
    for path, content in ((svg, svg_bytes), (png, png_bytes)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    return DiagramManifest([node["id"] for node in nodes], [edge["id"] for edge in edges], sources, provenance,
                           {"svg": sha256(svg_bytes).hexdigest(), "png": sha256(png_bytes).hexdigest()}, warnings)
