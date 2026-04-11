import json
import sys
import importlib
import subprocess
from shutil import which
from io import BytesIO
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from pypdf import PdfReader, PdfWriter



STANDARD_PDF_FONTS = {
    "Courier",
    "Courier-Bold",
    "Courier-Oblique",
    "Courier-BoldOblique",
    "Helvetica",
    "Helvetica-Bold",
    "Helvetica-Oblique",
    "Helvetica-BoldOblique",
    "Times-Roman",
    "Times-Bold",
    "Times-Italic",
    "Times-BoldItalic",
}

_CUSTOM_FONT_CACHE: Dict[str, str] = {}
_CID_FONT_READY = False
_RLPDFMETRICS = None
_RLCIDFONT = None
_RLTTFONT = None
_RLCANVAS = None
_LOCAL_CJK_FONT_SOURCE_CACHE: Optional[str] = None
_LOCAL_CJK_FONT_DISCOVERY_DONE = False

AUTO_DISCOVERY_FONT_EXTENSIONS = {".ttf", ".otf"}
CJK_FONT_HINTS = (
    "noto",
    "sourcehan",
    "source-han",
    "source han",
    "wqy",
    "wenquanyi",
    "sarasa",
    "lxgw",
    "pingfang",
    "heiti",
    "hiragino",
    "simhei",
    "simsun",
    "msyh",
)


def _load_reportlab() -> None:
    global _RLPDFMETRICS, _RLCIDFONT, _RLTTFONT, _RLCANVAS
    if _RLPDFMETRICS is not None and _RLCANVAS is not None:
        return

    try:
        _RLPDFMETRICS = importlib.import_module("reportlab.pdfbase.pdfmetrics")
        cidfonts = importlib.import_module("reportlab.pdfbase.cidfonts")
        ttfonts = importlib.import_module("reportlab.pdfbase.ttfonts")
        _RLCANVAS = importlib.import_module("reportlab.pdfgen.canvas")
        _RLCIDFONT = cidfonts.UnicodeCIDFont
        _RLTTFONT = ttfonts.TTFont
    except Exception as exc:
        raise RuntimeError(
            "This script requires reportlab. Install it with: pip install reportlab"
        ) from exc



def transform_from_image_coords(bbox, image_width, image_height, pdf_width, pdf_height):
    x_scale = pdf_width / image_width
    y_scale = pdf_height / image_height

    left = bbox[0] * x_scale
    right = bbox[2] * x_scale

    top = pdf_height - (bbox[1] * y_scale)
    bottom = pdf_height - (bbox[3] * y_scale)

    return left, bottom, right, top


def transform_from_pdf_coords(bbox, pdf_height):
    left = bbox[0]
    right = bbox[2]

    pypdf_top = pdf_height - bbox[1]      
    pypdf_bottom = pdf_height - bbox[3]   

    return left, pypdf_bottom, right, pypdf_top


def _ensure_cid_font() -> None:
    global _CID_FONT_READY
    _load_reportlab()
    if _CID_FONT_READY:
        return
    try:
        _RLPDFMETRICS.getFont("STSong-Light")
        _CID_FONT_READY = True
        return
    except KeyError:
        pass

    try:
        _RLPDFMETRICS.registerFont(_RLCIDFONT("STSong-Light"))
        _CID_FONT_READY = True
    except Exception:
        _CID_FONT_READY = False


def _has_non_ascii(text: str) -> bool:
    return any(ord(ch) > 127 for ch in text)


def _is_auto_discovery_font(path_str: str) -> bool:
    return Path(path_str).suffix.lower() in AUTO_DISCOVERY_FONT_EXTENSIONS


def _run_fc_list_zh() -> List[str]:
    if which("fc-list") is None:
        return []

    try:
        result = subprocess.run(
            ["fc-list", ":lang=zh", "-f", "%{file}\n"],
            capture_output=True,
            text=True,
            timeout=4,
            check=False,
        )
    except Exception:
        return []

    if result.returncode != 0:
        return []

    font_paths: List[str] = []
    seen = set()
    for line in result.stdout.splitlines():
        candidate = line.strip()
        if not candidate or candidate in seen:
            continue
        if not _is_auto_discovery_font(candidate):
            continue
        if not Path(candidate).exists():
            continue
        seen.add(candidate)
        font_paths.append(candidate)
    return font_paths


def _fallback_local_font_candidates() -> List[str]:
    common_candidates = [
        "/usr/share/fonts/opentype/noto/NotoSansCJKSC-Regular.otf",
        "/usr/share/fonts/truetype/noto/NotoSansSC-Regular.ttf",
        "/Library/Fonts/Arial Unicode.ttf",
        "C:/Windows/Fonts/simhei.ttf",
    ]

    existing = []
    for candidate in common_candidates:
        if Path(candidate).exists():
            existing.append(candidate)
    return existing


def _font_priority_key(path_str: str) -> Tuple[int, int]:
    lower_name = Path(path_str).name.lower()
    has_hint = any(hint in lower_name for hint in CJK_FONT_HINTS)
    ext = Path(path_str).suffix.lower()
    ext_rank = {".ttf": 0, ".otf": 1, ".ttc": 2}.get(ext, 3)
    hint_rank = 0 if has_hint else 1
    return hint_rank, ext_rank


def _iter_local_cjk_font_sources() -> List[str]:
    candidates = _run_fc_list_zh() + _fallback_local_font_candidates()

    deduped: List[str] = []
    seen = set()
    for path_str in candidates:
        if path_str in seen:
            continue
        seen.add(path_str)
        deduped.append(path_str)

    deduped.sort(key=_font_priority_key)

    return deduped


def _discover_local_cjk_font_source() -> Optional[str]:
    global _LOCAL_CJK_FONT_SOURCE_CACHE, _LOCAL_CJK_FONT_DISCOVERY_DONE
    if _LOCAL_CJK_FONT_SOURCE_CACHE:
        return _LOCAL_CJK_FONT_SOURCE_CACHE
    if _LOCAL_CJK_FONT_DISCOVERY_DONE:
        return None

    probe_text = "中文字体探测"
    for source in _iter_local_cjk_font_sources():
        try:
            font_name = _register_custom_font(source)
            # Ensure this font can actually measure CJK text.
            _RLPDFMETRICS.stringWidth(probe_text, font_name, 12)
            _LOCAL_CJK_FONT_SOURCE_CACHE = source
            _LOCAL_CJK_FONT_DISCOVERY_DONE = True
            return source
        except Exception:
            continue

    _LOCAL_CJK_FONT_DISCOVERY_DONE = True
    return None


def _parse_font_source(font_path: str, font_index: Optional[int]) -> Tuple[str, int]:
    source = str(font_path).strip()
    parsed_index = 0

    if "#" in source:
        base, maybe_index = source.rsplit("#", 1)
        if maybe_index.isdigit():
            source = base
            parsed_index = int(maybe_index)

    if source.lower().endswith(".ttc") and "," in source:
        base, maybe_index = source.rsplit(",", 1)
        if maybe_index.isdigit():
            source = base
            parsed_index = int(maybe_index)

    if font_index is not None:
        parsed_index = int(font_index)

    return source, parsed_index


def _register_custom_font(font_path: str, font_index: Optional[int] = None) -> str:
    _load_reportlab()
    normalized_path, normalized_index = _parse_font_source(font_path, font_index)
    resolved_path = Path(normalized_path).expanduser()
    if not resolved_path.exists():
        raise FileNotFoundError(f"Font file not found: {resolved_path}")

    resolved = str(resolved_path.resolve())
    cache_key = f"{resolved}#{normalized_index}"

    cached = _CUSTOM_FONT_CACHE.get(cache_key)
    if cached:
        return cached

    font_name = f"CustomFont_{abs(hash(cache_key))}"
    try:
        _RLPDFMETRICS.getFont(font_name)
    except KeyError:
        try:
            if resolved.lower().endswith(".ttc"):
                _RLPDFMETRICS.registerFont(_RLTTFONT(font_name, resolved, subfontIndex=normalized_index))
            else:
                _RLPDFMETRICS.registerFont(_RLTTFONT(font_name, resolved))
        except Exception as exc:
            if resolved.lower().endswith(".ttc"):
                raise RuntimeError(
                    "Failed to load TTC font. In the AstrBot sandbox, macOS TTC fonts often use PostScript outlines unsupported by reportlab. Prefer a compatible .ttf font or the Chinese-only STSong-Light fallback."
                ) from exc
            raise

    _CUSTOM_FONT_CACHE[cache_key] = font_name
    return font_name


def _resolve_font(entry_text: dict, text: str) -> str:
    _load_reportlab()
    font_path = entry_text.get("font_path")
    font_index = entry_text.get("font_index")
    if font_path:
        return _register_custom_font(font_path, font_index)

    requested = entry_text.get("font", "Helvetica")
    if requested in STANDARD_PDF_FONTS:
        return requested
    try:
        _RLPDFMETRICS.getFont(requested)
        return requested
    except KeyError:
        pass

    if _has_non_ascii(text):
        discovered_source = _discover_local_cjk_font_source()
        if discovered_source:
            try:
                return _register_custom_font(discovered_source)
            except Exception:
                pass

        _ensure_cid_font()
        if _CID_FONT_READY:
            return "STSong-Light"

        raise RuntimeError(
            "No usable font found for non-ASCII text. Provide entry_text.font_path to a compatible .ttf font, or limit the document to Chinese text and use a CID fallback."
        )

    return "Helvetica"


def _parse_hex_color(color_value: str) -> Tuple[float, float, float]:
    normalized = str(color_value).strip().lstrip("#")
    if len(normalized) != 6:
        return 0.0, 0.0, 0.0
    try:
        red = int(normalized[0:2], 16) / 255.0
        green = int(normalized[2:4], 16) / 255.0
        blue = int(normalized[4:6], 16) / 255.0
    except ValueError:
        return 0.0, 0.0, 0.0
    return red, green, blue


def _wrap_text(text: str, font_name: str, font_size: float, max_width: float) -> List[str]:
    _load_reportlab()
    if max_width <= 1:
        return [text]

    wrapped_lines: List[str] = []
    source_lines = text.splitlines() or [""]
    for src in source_lines:
        if not src:
            wrapped_lines.append("")
            continue
        current = ""
        for ch in src:
            candidate = current + ch
            if current and _RLPDFMETRICS.stringWidth(candidate, font_name, font_size) > max_width:
                wrapped_lines.append(current)
                current = ch
            else:
                current = candidate
        if current:
            wrapped_lines.append(current)

    return wrapped_lines or [""]


def _draw_text_in_box(page_canvas: Any, rect: Tuple[float, float, float, float], entry_text: dict) -> None:
    text = str(entry_text.get("text", ""))
    if not text:
        return

    left, bottom, right, top = rect
    box_width = max(1.0, float(right) - float(left))
    box_height = max(1.0, float(top) - float(bottom))

    font_size = float(entry_text.get("font_size", 12))
    font_name = _resolve_font(entry_text, text)
    red, green, blue = _parse_hex_color(entry_text.get("font_color", "000000"))

    padding = 1.0
    max_text_width = max(1.0, box_width - (padding * 2))
    lines = _wrap_text(text, font_name, font_size, max_text_width)
    line_height = font_size * 1.2
    max_lines = max(1, int((box_height - (padding * 2)) / line_height))
    visible_lines = lines[:max_lines]

    page_canvas.setFillColorRGB(red, green, blue)
    page_canvas.setFont(font_name, font_size)

    y = float(top) - padding - font_size
    min_y = float(bottom) + padding
    for line in visible_lines:
        if y < min_y:
            break
        page_canvas.drawString(float(left) + padding, y, line)
        y -= line_height


def _transform_entry_box(field: dict, page_info: dict, pdf_width: float, pdf_height: float):
    if "pdf_width" in page_info:
        return transform_from_pdf_coords(
            field["entry_bounding_box"],
            float(pdf_height),
        )

    image_width = page_info["image_width"]
    image_height = page_info["image_height"]
    return transform_from_image_coords(
        field["entry_bounding_box"],
        image_width,
        image_height,
        float(pdf_width),
        float(pdf_height),
    )


def _build_overlay_pdf(reader: PdfReader, fields_data: dict) -> Tuple[PdfReader, int]:
    _load_reportlab()
    page_info_by_number = {p["page_number"]: p for p in fields_data.get("pages", [])}
    draw_items_by_page: Dict[int, List[Tuple[Tuple[float, float, float, float], dict]]] = {}

    for field in fields_data.get("form_fields", []):
        page_num = field.get("page_number")
        if not page_num or page_num < 1 or page_num > len(reader.pages):
            continue
        if "entry_text" not in field or "text" not in field["entry_text"]:
            continue
        if not field["entry_text"].get("text"):
            continue

        page_info = page_info_by_number.get(page_num)
        if not page_info:
            continue

        page = reader.pages[page_num - 1]
        pdf_width = float(page.mediabox.width)
        pdf_height = float(page.mediabox.height)
        transformed_entry_box = _transform_entry_box(field, page_info, pdf_width, pdf_height)

        draw_items_by_page.setdefault(page_num, []).append((transformed_entry_box, field["entry_text"]))

    packet = BytesIO()
    overlay_canvas = _RLCANVAS.Canvas(packet)
    total_draw_items = 0

    for page_num in range(1, len(reader.pages) + 1):
        page = reader.pages[page_num - 1]
        width = float(page.mediabox.width)
        height = float(page.mediabox.height)
        overlay_canvas.setPageSize((width, height))

        for rect, entry_text in draw_items_by_page.get(page_num, []):
            _draw_text_in_box(overlay_canvas, rect, entry_text)
            total_draw_items += 1

        overlay_canvas.showPage()

    overlay_canvas.save()
    packet.seek(0)
    return PdfReader(packet), total_draw_items


def fill_pdf_form(input_pdf_path, fields_json_path, output_pdf_path):
    
    with open(fields_json_path, "r") as f:
        fields_data = json.load(f)
    
    reader = PdfReader(input_pdf_path)
    overlay_reader, draw_count = _build_overlay_pdf(reader, fields_data)

    writer = PdfWriter()
    for i, base_page in enumerate(reader.pages):
        overlay_page = overlay_reader.pages[i]
        base_page.merge_page(overlay_page)
        writer.add_page(base_page)

    with open(output_pdf_path, "wb") as output:
        writer.write(output)
    
    print(f"Successfully filled PDF form and saved to {output_pdf_path}")
    print(f"Rendered {draw_count} text boxes into page content")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: fill_pdf_form_with_annotations.py [input pdf] [fields.json] [output pdf]")
        sys.exit(1)
    input_pdf = sys.argv[1]
    fields_json = sys.argv[2]
    output_pdf = sys.argv[3]
    
    fill_pdf_form(input_pdf, fields_json, output_pdf)
