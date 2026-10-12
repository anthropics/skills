#!/usr/bin/env python3
"""
Figma-to-Code Generator

Converts Figma node JSON into code for multiple frameworks:
Tailwind/HTML, React (JSX), Vue (SFC), Svelte, React Native, Flutter, plain CSS.

Usage:
    python3 figma_to_code.py --framework tailwind --input node.json
    python3 figma_to_code.py --framework react --input node.json --name MyComponent
    cat node.json | python3 figma_to_code.py --framework flutter

Part of the Figma Skill for Claude Code.
Requires: Python 3.8+ (stdlib only, no pip dependencies)
"""

import json
import sys
import argparse
import re
from pathlib import Path


# ---------------------------------------------------------------------------
# Load framework mappings
# ---------------------------------------------------------------------------

DATA_DIR = Path(__file__).parent.parent / "data"

def load_mappings() -> dict:
    """Load framework-mappings.json from the data directory."""
    mappings_file = DATA_DIR / "framework-mappings.json"
    if not mappings_file.exists():
        print(f"Error: {mappings_file} not found.", file=sys.stderr)
        print("Make sure the data/ directory is alongside the scripts/ directory.", file=sys.stderr)
        sys.exit(1)
    return json.loads(mappings_file.read_text(encoding="utf-8"))


MAPPINGS = None  # Lazy loaded


def get_mappings() -> dict:
    global MAPPINGS
    if MAPPINGS is None:
        MAPPINGS = load_mappings()
    return MAPPINGS


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def slugify(name: str) -> str:
    """Convert Figma layer name to a valid identifier."""
    return re.sub(r"[^a-zA-Z0-9]+", "-", name.strip()).strip("-").lower()


def pascal_case(name: str) -> str:
    """Convert to PascalCase for component names."""
    parts = re.sub(r"[^a-zA-Z0-9]+", " ", name.strip()).split()
    return "".join(w.capitalize() for w in parts) or "Component"


def camel_case(name: str) -> str:
    """Convert to camelCase."""
    pc = pascal_case(name)
    return pc[0].lower() + pc[1:] if pc else "component"


def figma_color_to_hex(color: dict) -> str:
    """Convert Figma RGBA floats to hex."""
    r = round(color.get("r", 0) * 255)
    g = round(color.get("g", 0) * 255)
    b = round(color.get("b", 0) * 255)
    a = color.get("a", 1)
    if a < 1:
        return f"#{r:02x}{g:02x}{b:02x}{round(a * 255):02x}"
    return f"#{r:02x}{g:02x}{b:02x}"


def figma_color_to_rgba_str(color: dict) -> str:
    """Convert Figma RGBA floats to rgba() string."""
    r = round(color.get("r", 0) * 255)
    g = round(color.get("g", 0) * 255)
    b = round(color.get("b", 0) * 255)
    a = round(color.get("a", 1), 3)
    if a == 1:
        return f"rgb({r}, {g}, {b})"
    return f"rgba({r}, {g}, {b}, {a})"


def closest_tw_spacing(px: float) -> str:
    """Find the closest Tailwind spacing class value for a pixel amount."""
    scales = get_mappings()["figma_scales"]["spacing"]
    closest_key = min(scales.keys(), key=lambda k: abs(int(k) - px))
    return scales[closest_key]


def closest_tw_font_size(px: float) -> str:
    """Find closest Tailwind text-* class for a font size."""
    scales = get_mappings()["figma_scales"]["fontSize"]
    closest_key = min(scales.keys(), key=lambda k: abs(int(k) - px))
    return scales[closest_key]


def closest_tw_font_weight(weight: int) -> str:
    """Find closest Tailwind font weight name."""
    scales = get_mappings()["figma_scales"]["fontWeight"]
    closest_key = min(scales.keys(), key=lambda k: abs(int(k) - weight))
    return scales[closest_key]


def closest_tw_radius(px: float) -> str:
    """Find closest Tailwind rounded-* class."""
    scales = get_mappings()["figma_scales"]["borderRadius"]
    closest_key = min(scales.keys(), key=lambda k: abs(int(k) - px))
    val = scales[closest_key]
    if val == "DEFAULT":
        return "rounded"
    if val == "none":
        return "rounded-none"
    return f"rounded-{val}"


def closest_tw_shadow(blur: float) -> str:
    """Find closest Tailwind shadow class."""
    scales = get_mappings()["figma_scales"]["shadow"]
    closest_key = min(scales.keys(), key=lambda k: abs(int(k) - blur))
    val = scales[closest_key]
    if val == "DEFAULT":
        return "shadow"
    return f"shadow-{val}"


# ---------------------------------------------------------------------------
# FigmaNode wrapper
# ---------------------------------------------------------------------------

class FigmaNode:
    """Convenience wrapper around a Figma JSON node."""

    def __init__(self, data: dict):
        self._data = data

    @property
    def name(self) -> str:
        return self._data.get("name", "Untitled")

    @property
    def type(self) -> str:
        return self._data.get("type", "FRAME")

    @property
    def layout_mode(self):
        return self._data.get("layoutMode")

    @property
    def primary_axis_align(self) -> str:
        return self._data.get("primaryAxisAlignItems", "MIN")

    @property
    def counter_axis_align(self) -> str:
        return self._data.get("counterAxisAlignItems", "MIN")

    @property
    def padding(self) -> dict:
        return {
            "top": self._data.get("paddingTop", 0),
            "right": self._data.get("paddingRight", 0),
            "bottom": self._data.get("paddingBottom", 0),
            "left": self._data.get("paddingLeft", 0),
        }

    @property
    def gap(self) -> float:
        return self._data.get("itemSpacing", 0)

    @property
    def width(self) -> float:
        bbox = self._data.get("absoluteBoundingBox", {})
        return bbox.get("width", 0)

    @property
    def height(self) -> float:
        bbox = self._data.get("absoluteBoundingBox", {})
        return bbox.get("height", 0)

    @property
    def corner_radius(self):
        return self._data.get("cornerRadius")

    @property
    def corner_radii(self):
        return self._data.get("rectangleCornerRadii")

    @property
    def fills(self) -> list:
        return [f for f in self._data.get("fills", []) if f.get("visible", True)]

    @property
    def strokes(self) -> list:
        return [s for s in self._data.get("strokes", []) if s.get("visible", True)]

    @property
    def stroke_weight(self) -> float:
        return self._data.get("strokeWeight", 0)

    @property
    def effects(self) -> list:
        return [e for e in self._data.get("effects", []) if e.get("visible", True)]

    @property
    def opacity(self) -> float:
        return self._data.get("opacity", 1)

    @property
    def text_style(self) -> dict:
        return self._data.get("style", {})

    @property
    def characters(self) -> str:
        return self._data.get("characters", "")

    @property
    def children(self) -> list:
        return [FigmaNode(c) for c in self._data.get("children", [])]

    @property
    def sizing_horizontal(self) -> str:
        return self._data.get("layoutSizingHorizontal", "FIXED")

    @property
    def sizing_vertical(self) -> str:
        return self._data.get("layoutSizingVertical", "FIXED")

    @property
    def overflow(self) -> str:
        return self._data.get("clipsContent", False)


# ---------------------------------------------------------------------------
# Code generators
# ---------------------------------------------------------------------------

class TailwindGenerator:
    """Generate Tailwind/HTML code from Figma nodes."""

    def __init__(self, jsx: bool = False):
        self.attr = "className" if jsx else "class"

    def generate(self, node: FigmaNode, indent: int = 0) -> str:
        if node.type == "TEXT":
            return self._text(node, indent)
        return self._container(node, indent)

    def _classes(self, node: FigmaNode) -> list:
        cls = []
        mappings = get_mappings()["frameworks"]["tailwind"]

        # Layout
        if node.layout_mode:
            layout_cls = mappings["layout"].get(node.layout_mode, "")
            cls.extend(layout_cls.split())
            align_main = mappings["mainAxisAlign"].get(node.primary_axis_align, "")
            align_cross = mappings["crossAxisAlign"].get(node.counter_axis_align, "")
            if align_main:
                cls.append(align_main)
            if align_cross:
                cls.append(align_cross)

        # Gap
        if node.gap:
            cls.append(f"gap-{closest_tw_spacing(node.gap)}")

        # Padding
        p = node.padding
        if p["top"] == p["right"] == p["bottom"] == p["left"] and p["top"] > 0:
            cls.append(f"p-{closest_tw_spacing(p['top'])}")
        else:
            if p["top"]:
                cls.append(f"pt-{closest_tw_spacing(p['top'])}")
            if p["right"]:
                cls.append(f"pr-{closest_tw_spacing(p['right'])}")
            if p["bottom"]:
                cls.append(f"pb-{closest_tw_spacing(p['bottom'])}")
            if p["left"]:
                cls.append(f"pl-{closest_tw_spacing(p['left'])}")

        # Sizing
        if node.sizing_horizontal == "FILL":
            cls.append("w-full")
        elif node.sizing_horizontal == "HUG":
            cls.append("w-fit")

        # Corner radius
        if node.corner_radius is not None and node.corner_radius > 0:
            cls.append(closest_tw_radius(node.corner_radius))

        # Background
        for fill in node.fills:
            if fill.get("type") == "SOLID":
                color = fill.get("color", {})
                hex_color = figma_color_to_hex(color)
                cls.append(f"bg-[{hex_color}]")
                break

        # Border
        if node.strokes and node.stroke_weight:
            cls.append(f"border-{max(1, round(node.stroke_weight))}" if node.stroke_weight > 1 else "border")
            for stroke in node.strokes:
                if stroke.get("type") == "SOLID":
                    hex_color = figma_color_to_hex(stroke.get("color", {}))
                    cls.append(f"border-[{hex_color}]")
                    break

        # Shadow
        for effect in node.effects:
            if effect.get("type") == "DROP_SHADOW":
                cls.append(closest_tw_shadow(effect.get("radius", 4)))
                break

        # Opacity
        if node.opacity < 1:
            scales = get_mappings()["figma_scales"]["opacity"]
            closest_key = min(scales.keys(), key=lambda k: abs(float(k) - node.opacity))
            cls.append(f"opacity-{scales[closest_key]}")

        # Overflow
        if node.overflow:
            cls.append("overflow-hidden")

        return cls

    def _text_classes(self, node: FigmaNode) -> list:
        cls = []
        style = node.text_style

        # Font size
        fs = style.get("fontSize", 16)
        cls.append(f"text-{closest_tw_font_size(fs)}")

        # Font weight
        fw = style.get("fontWeight", 400)
        cls.append(f"font-{closest_tw_font_weight(fw)}")

        # Text color
        for fill in node.fills:
            if fill.get("type") == "SOLID":
                hex_color = figma_color_to_hex(fill.get("color", {}))
                cls.append(f"text-[{hex_color}]")
                break

        # Text align
        mappings = get_mappings()["frameworks"]["tailwind"]
        align = style.get("textAlignHorizontal", "LEFT")
        if align in mappings.get("textAlign", {}):
            cls.append(mappings["textAlign"][align])

        # Line height
        lh_px = style.get("lineHeightPx")
        if lh_px and fs:
            ratio = round(lh_px / fs, 3)
            lh_scales = get_mappings()["figma_scales"]["lineHeight"]
            closest_key = min(lh_scales.keys(), key=lambda k: abs(float(k) - ratio))
            cls.append(f"leading-{lh_scales[closest_key]}")

        # Letter spacing
        ls = style.get("letterSpacing", 0)
        if ls and fs:
            em = round(ls / fs, 4)
            ls_scales = get_mappings()["figma_scales"]["letterSpacing"]
            closest_key = min(ls_scales.keys(), key=lambda k: abs(float(k) - em))
            cls.append(f"tracking-{ls_scales[closest_key]}")

        return cls

    def _text(self, node: FigmaNode, indent: int) -> str:
        cls = self._text_classes(node)
        pad = "  " * indent
        class_str = " ".join(cls)
        text = node.characters or "Text"
        return f'{pad}<p {self.attr}="{class_str}">{text}</p>'

    def _container(self, node: FigmaNode, indent: int) -> str:
        cls = self._classes(node)
        pad = "  " * indent
        class_str = " ".join(cls)
        tag = "section" if node.type == "SECTION" else "div"

        children_code = []
        for child in node.children:
            children_code.append(self.generate(child, indent + 1))

        if children_code:
            inner = "\n".join(children_code)
            return f'{pad}<{tag} {self.attr}="{class_str}">\n{inner}\n{pad}</{tag}>'
        return f'{pad}<{tag} {self.attr}="{class_str}"></{tag}>'


class ReactGenerator:
    """Generate React JSX + Tailwind component."""

    def __init__(self):
        self.tw = TailwindGenerator(jsx=True)

    def generate(self, node: FigmaNode, component_name: str = None) -> str:
        name = component_name or pascal_case(node.name)
        body = self.tw.generate(node, indent=2)

        return (
            f"export default function {name}() {{\n"
            f"  return (\n"
            f"{body}\n"
            f"  );\n"
            f"}}\n"
        )


class VueGenerator:
    """Generate Vue SFC component."""

    def __init__(self):
        self.tw = TailwindGenerator()

    def generate(self, node: FigmaNode, component_name: str = None) -> str:
        name = component_name or pascal_case(node.name)
        template = self.tw.generate(node, indent=1)

        return (
            f"<script setup lang=\"ts\">\n"
            f"// {name} — generated from Figma\n"
            f"</script>\n"
            f"\n"
            f"<template>\n"
            f"{template}\n"
            f"</template>\n"
        )


class SvelteGenerator:
    """Generate Svelte component."""

    def __init__(self):
        self.tw = TailwindGenerator()

    def generate(self, node: FigmaNode, component_name: str = None) -> str:
        name = component_name or pascal_case(node.name)
        template = self.tw.generate(node, indent=0)

        return (
            f"<script lang=\"ts\">\n"
            f"  // {name} — generated from Figma\n"
            f"</script>\n"
            f"\n"
            f"{template}\n"
        )


class CSSGenerator:
    """Generate plain HTML + CSS."""

    def generate(self, node: FigmaNode, indent: int = 0) -> str:
        css_rules = []
        html = self._node_html(node, indent, css_rules)

        css_block = "\n\n".join(css_rules)
        return f"<style>\n{css_block}\n</style>\n\n{html}"

    def _css_props(self, node: FigmaNode) -> dict:
        props = {}

        # Layout
        if node.layout_mode:
            props["display"] = "flex"
            props["flex-direction"] = "row" if node.layout_mode == "HORIZONTAL" else "column"

            align_map = {"MIN": "flex-start", "CENTER": "center", "MAX": "flex-end", "SPACE_BETWEEN": "space-between"}
            cross_map = {"MIN": "flex-start", "CENTER": "center", "MAX": "flex-end", "STRETCH": "stretch", "BASELINE": "baseline"}
            props["justify-content"] = align_map.get(node.primary_axis_align, "flex-start")
            props["align-items"] = cross_map.get(node.counter_axis_align, "flex-start")

        # Gap
        if node.gap:
            props["gap"] = f"{node.gap}px"

        # Padding
        p = node.padding
        if p["top"] == p["right"] == p["bottom"] == p["left"] and p["top"] > 0:
            props["padding"] = f"{p['top']}px"
        elif any(v for v in p.values()):
            props["padding"] = f"{p['top']}px {p['right']}px {p['bottom']}px {p['left']}px"

        # Sizing
        if node.sizing_horizontal == "FILL":
            props["width"] = "100%"

        # Border radius
        if node.corner_radius is not None and node.corner_radius > 0:
            props["border-radius"] = f"{node.corner_radius}px"

        # Background
        for fill in node.fills:
            if fill.get("type") == "SOLID":
                props["background-color"] = figma_color_to_hex(fill.get("color", {}))
                break

        # Border
        if node.strokes and node.stroke_weight:
            for stroke in node.strokes:
                if stroke.get("type") == "SOLID":
                    hex_c = figma_color_to_hex(stroke.get("color", {}))
                    props["border"] = f"{node.stroke_weight}px solid {hex_c}"
                    break

        # Shadow
        for effect in node.effects:
            if effect.get("type") == "DROP_SHADOW":
                color = figma_color_to_rgba_str(effect.get("color", {}))
                x = effect.get("offset", {}).get("x", 0)
                y = effect.get("offset", {}).get("y", 0)
                blur = effect.get("radius", 0)
                spread = effect.get("spread", 0)
                props["box-shadow"] = f"{x}px {y}px {blur}px {spread}px {color}"
                break

        # Opacity
        if node.opacity < 1:
            props["opacity"] = str(round(node.opacity, 2))

        # Overflow
        if node.overflow:
            props["overflow"] = "hidden"

        return props

    def _text_css_props(self, node: FigmaNode) -> dict:
        props = {}
        style = node.text_style

        fs = style.get("fontSize", 16)
        props["font-size"] = f"{fs}px"
        props["font-weight"] = str(style.get("fontWeight", 400))
        props["font-family"] = f"'{style.get('fontFamily', 'sans-serif')}', sans-serif"

        lh = style.get("lineHeightPx")
        if lh:
            props["line-height"] = f"{round(lh, 1)}px"

        ls = style.get("letterSpacing", 0)
        if ls:
            props["letter-spacing"] = f"{round(ls, 2)}px"

        align_map = {"LEFT": "left", "CENTER": "center", "RIGHT": "right", "JUSTIFIED": "justify"}
        align = style.get("textAlignHorizontal", "LEFT")
        if align in align_map:
            props["text-align"] = align_map[align]

        # Text color
        for fill in node.fills:
            if fill.get("type") == "SOLID":
                props["color"] = figma_color_to_hex(fill.get("color", {}))
                break

        return props

    def _node_html(self, node: FigmaNode, indent: int, css_rules: list) -> str:
        class_name = slugify(node.name) or "element"
        pad = "  " * indent

        if node.type == "TEXT":
            props = self._text_css_props(node)
            css = f".{class_name} {{\n" + "\n".join(f"  {k}: {v};" for k, v in props.items()) + "\n}"
            css_rules.append(css)
            text = node.characters or "Text"
            return f'{pad}<p class="{class_name}">{text}</p>'

        props = self._css_props(node)
        if props:
            css = f".{class_name} {{\n" + "\n".join(f"  {k}: {v};" for k, v in props.items()) + "\n}"
            css_rules.append(css)

        children_code = []
        for child in node.children:
            children_code.append(self._node_html(child, indent + 1, css_rules))

        tag = "section" if node.type == "SECTION" else "div"
        if children_code:
            inner = "\n".join(children_code)
            return f'{pad}<{tag} class="{class_name}">\n{inner}\n{pad}</{tag}>'
        return f'{pad}<{tag} class="{class_name}"></{tag}>'


class ReactNativeGenerator:
    """Generate React Native component with StyleSheet."""

    def generate(self, node: FigmaNode, component_name: str = None) -> str:
        name = component_name or pascal_case(node.name)
        styles = {}
        jsx = self._node_jsx(node, 2, styles)

        style_lines = []
        for style_name, props in styles.items():
            prop_str = ",\n    ".join(f"{k}: {v}" for k, v in props.items())
            style_lines.append(f"  {style_name}: {{\n    {prop_str},\n  }}")

        styles_block = ",\n".join(style_lines)

        return (
            f"import React from 'react';\n"
            f"import {{ View, Text, StyleSheet }} from 'react-native';\n"
            f"\n"
            f"export default function {name}() {{\n"
            f"  return (\n"
            f"{jsx}\n"
            f"  );\n"
            f"}}\n"
            f"\n"
            f"const styles = StyleSheet.create({{\n"
            f"{styles_block},\n"
            f"}});\n"
        )

    def _style_props(self, node: FigmaNode) -> dict:
        props = {}

        if node.layout_mode:
            props["flexDirection"] = "'row'" if node.layout_mode == "HORIZONTAL" else "'column'"
            align_map = {"MIN": "'flex-start'", "CENTER": "'center'", "MAX": "'flex-end'", "SPACE_BETWEEN": "'space-between'"}
            cross_map = {"MIN": "'flex-start'", "CENTER": "'center'", "MAX": "'flex-end'", "STRETCH": "'stretch'"}
            props["justifyContent"] = align_map.get(node.primary_axis_align, "'flex-start'")
            props["alignItems"] = cross_map.get(node.counter_axis_align, "'flex-start'")

        if node.gap:
            props["gap"] = str(round(node.gap))

        p = node.padding
        if p["top"] == p["right"] == p["bottom"] == p["left"] and p["top"] > 0:
            props["padding"] = str(round(p["top"]))
        elif any(v for v in p.values()):
            if p["top"]: props["paddingTop"] = str(round(p["top"]))
            if p["right"]: props["paddingRight"] = str(round(p["right"]))
            if p["bottom"]: props["paddingBottom"] = str(round(p["bottom"]))
            if p["left"]: props["paddingLeft"] = str(round(p["left"]))

        if node.sizing_horizontal == "FILL":
            props["flex"] = "1"

        if node.corner_radius is not None and node.corner_radius > 0:
            props["borderRadius"] = str(round(node.corner_radius))

        for fill in node.fills:
            if fill.get("type") == "SOLID":
                props["backgroundColor"] = f"'{figma_color_to_hex(fill.get('color', {}))}'"
                break

        if node.strokes and node.stroke_weight:
            props["borderWidth"] = str(round(node.stroke_weight))
            for stroke in node.strokes:
                if stroke.get("type") == "SOLID":
                    props["borderColor"] = f"'{figma_color_to_hex(stroke.get('color', {}))}'"
                    break

        for effect in node.effects:
            if effect.get("type") == "DROP_SHADOW":
                props["shadowOffset"] = f"{{ width: {effect.get('offset', {}).get('x', 0)}, height: {effect.get('offset', {}).get('y', 0)} }}"
                props["shadowRadius"] = str(effect.get("radius", 0))
                props["shadowOpacity"] = str(round(effect.get("color", {}).get("a", 0.25), 2))
                props["elevation"] = str(max(1, round(effect.get("radius", 0) / 2)))
                break

        if node.opacity < 1:
            props["opacity"] = str(round(node.opacity, 2))

        return props

    def _text_style_props(self, node: FigmaNode) -> dict:
        props = {}
        style = node.text_style

        props["fontSize"] = str(style.get("fontSize", 16))
        fw = style.get("fontWeight", 400)
        props["fontWeight"] = f"'{fw}'"

        for fill in node.fills:
            if fill.get("type") == "SOLID":
                props["color"] = f"'{figma_color_to_hex(fill.get('color', {}))}'"
                break

        lh = style.get("lineHeightPx")
        if lh:
            props["lineHeight"] = str(round(lh))

        ls = style.get("letterSpacing", 0)
        if ls:
            props["letterSpacing"] = str(round(ls, 1))

        align_map = {"LEFT": "'left'", "CENTER": "'center'", "RIGHT": "'right'"}
        align = style.get("textAlignHorizontal", "LEFT")
        if align in align_map:
            props["textAlign"] = align_map[align]

        return props

    def _node_jsx(self, node: FigmaNode, indent: int, styles: dict) -> str:
        pad = "  " * indent
        style_name = camel_case(node.name) or "container"

        # Ensure unique style names
        base_name = style_name
        counter = 1
        while style_name in styles:
            style_name = f"{base_name}{counter}"
            counter += 1

        if node.type == "TEXT":
            props = self._text_style_props(node)
            styles[style_name] = props
            text = node.characters or "Text"
            return f'{pad}<Text style={{styles.{style_name}}}>{text}</Text>'

        props = self._style_props(node)
        styles[style_name] = props

        children_code = []
        for child in node.children:
            children_code.append(self._node_jsx(child, indent + 1, styles))

        if children_code:
            inner = "\n".join(children_code)
            return f'{pad}<View style={{styles.{style_name}}}>\n{inner}\n{pad}</View>'
        return f'{pad}<View style={{styles.{style_name}}} />'


class FlutterGenerator:
    """Generate Flutter/Dart widget code."""

    def generate(self, node: FigmaNode, component_name: str = None) -> str:
        name = component_name or pascal_case(node.name)
        body = self._node_dart(node, 2)

        return (
            f"import 'package:flutter/material.dart';\n"
            f"\n"
            f"class {name} extends StatelessWidget {{\n"
            f"  const {name}({{super.key}});\n"
            f"\n"
            f"  @override\n"
            f"  Widget build(BuildContext context) {{\n"
            f"    return {body.strip()};\n"
            f"  }}\n"
            f"}}\n"
        )

    def _node_dart(self, node: FigmaNode, indent: int) -> str:
        pad = "  " * indent

        if node.type == "TEXT":
            return self._text_dart(node, indent)

        # Build decoration
        decoration_parts = []
        for fill in node.fills:
            if fill.get("type") == "SOLID":
                hex_c = figma_color_to_hex(fill.get("color", {}))
                decoration_parts.append(f"color: Color(0xFF{hex_c[1:7].upper()})")
                break

        if node.corner_radius is not None and node.corner_radius > 0:
            decoration_parts.append(f"borderRadius: BorderRadius.circular({node.corner_radius})")

        for effect in node.effects:
            if effect.get("type") == "DROP_SHADOW":
                x = effect.get("offset", {}).get("x", 0)
                y = effect.get("offset", {}).get("y", 0)
                blur = effect.get("radius", 0)
                color = effect.get("color", {})
                a = round(color.get("a", 0.25), 2)
                decoration_parts.append(
                    f"boxShadow: [BoxShadow(offset: Offset({x}, {y}), blurRadius: {blur}, color: Colors.black.withValues(alpha: {a}))]"
                )
                break

        if node.strokes and node.stroke_weight:
            for stroke in node.strokes:
                if stroke.get("type") == "SOLID":
                    hex_c = figma_color_to_hex(stroke.get("color", {}))
                    decoration_parts.append(
                        f"border: Border.all(color: Color(0xFF{hex_c[1:7].upper()}), width: {node.stroke_weight})"
                    )
                    break

        # Build padding
        p = node.padding
        padding_str = ""
        if p["top"] == p["right"] == p["bottom"] == p["left"] and p["top"] > 0:
            padding_str = f"EdgeInsets.all({p['top']})"
        elif any(v for v in p.values()):
            padding_str = f"EdgeInsets.fromLTRB({p['left']}, {p['top']}, {p['right']}, {p['bottom']})"

        # Build children
        children_dart = []
        for child in node.children:
            children_dart.append(self._node_dart(child, indent + 2))

        # Choose widget
        mappings = get_mappings()["frameworks"]["flutter"]
        layout_widget = mappings["layout"].get(node.layout_mode, "Container") if node.layout_mode else "Container"

        if layout_widget in ("Row", "Column"):
            main_align = mappings["mainAxisAlign"].get(node.primary_axis_align, "MainAxisAlignment.start")
            cross_align = mappings["crossAxisAlign"].get(node.counter_axis_align, "CrossAxisAlignment.start")

            inner_children = (",\n").join(c.strip() for c in children_dart)

            # Wrap in Container for decoration/padding
            layout_code = f"{pad}{layout_widget}(\n"
            layout_code += f"{pad}  mainAxisAlignment: {main_align},\n"
            layout_code += f"{pad}  crossAxisAlignment: {cross_align},\n"
            if node.gap:
                # Use SizedBox spacing
                spaced = []
                for i, c in enumerate(children_dart):
                    spaced.append(c.strip())
                    if i < len(children_dart) - 1:
                        dim = "height" if layout_widget == "Column" else "width"
                        spaced.append(f"SizedBox({dim}: {node.gap})")
                inner_children = (",\n" + pad + "    ").join(spaced)
            layout_code += f"{pad}  children: [\n{pad}    {inner_children},\n{pad}  ],\n"
            layout_code += f"{pad})"

            if decoration_parts or padding_str:
                wrap = f"{pad}Container(\n"
                if padding_str:
                    wrap += f"{pad}  padding: {padding_str},\n"
                if decoration_parts:
                    dec_str = ", ".join(decoration_parts)
                    wrap += f"{pad}  decoration: BoxDecoration({dec_str}),\n"
                wrap += f"{pad}  child: {layout_code.strip()},\n"
                wrap += f"{pad})"
                return wrap
            return layout_code

        # Container (no auto-layout)
        code = f"{pad}Container(\n"
        if padding_str:
            code += f"{pad}  padding: {padding_str},\n"
        if decoration_parts:
            dec_str = ", ".join(decoration_parts)
            code += f"{pad}  decoration: BoxDecoration({dec_str}),\n"
        if node.width:
            code += f"{pad}  width: {node.width},\n"
        if node.height:
            code += f"{pad}  height: {node.height},\n"
        if children_dart:
            code += f"{pad}  child: {children_dart[0].strip()},\n"
        code += f"{pad})"
        return code

    def _text_dart(self, node: FigmaNode, indent: int) -> str:
        pad = "  " * indent
        style = node.text_style
        text = node.characters or "Text"

        parts = []
        fs = style.get("fontSize", 16)
        parts.append(f"fontSize: {fs}")
        fw = style.get("fontWeight", 400)
        fw_map = {100: "w100", 200: "w200", 300: "w300", 400: "w400", 500: "w500", 600: "w600", 700: "w700", 800: "w800", 900: "w900"}
        closest_fw = min(fw_map.keys(), key=lambda k: abs(k - fw))
        parts.append(f"fontWeight: FontWeight.{fw_map[closest_fw]}")

        for fill in node.fills:
            if fill.get("type") == "SOLID":
                hex_c = figma_color_to_hex(fill.get("color", {}))
                parts.append(f"color: Color(0xFF{hex_c[1:7].upper()})")
                break

        lh = style.get("lineHeightPx")
        if lh and fs:
            parts.append(f"height: {round(lh / fs, 2)}")

        ls = style.get("letterSpacing", 0)
        if ls:
            parts.append(f"letterSpacing: {round(ls, 1)}")

        style_str = ", ".join(parts)
        return f"{pad}Text(\n{pad}  '{text}',\n{pad}  style: TextStyle({style_str}),\n{pad})"


# ---------------------------------------------------------------------------
# Generator registry
# ---------------------------------------------------------------------------

GENERATORS = {
    "tailwind": TailwindGenerator,
    "react": ReactGenerator,
    "vue": VueGenerator,
    "svelte": SvelteGenerator,
    "react-native": ReactNativeGenerator,
    "flutter": FlutterGenerator,
    "css": CSSGenerator,
}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Convert Figma node JSON to code for multiple frameworks.",
        epilog="Part of the Figma Skill for Claude Code — https://github.com/figma-skill",
    )
    parser.add_argument(
        "--framework", "-f",
        choices=list(GENERATORS.keys()),
        default="tailwind",
        help="Target framework (default: tailwind)",
    )
    parser.add_argument(
        "--input", "-i",
        help="Path to Figma node JSON file (or pipe via stdin)",
    )
    parser.add_argument(
        "--name", "-n",
        help="Component name (default: derived from Figma layer name)",
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)",
    )
    args = parser.parse_args()

    # Read input
    if args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"Error: File not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        data = json.loads(path.read_text(encoding="utf-8"))
    elif not sys.stdin.isatty():
        data = json.load(sys.stdin)
    else:
        parser.print_help()
        print("\nError: Provide --input file or pipe JSON via stdin.", file=sys.stderr)
        sys.exit(1)

    # Handle Figma API response formats
    if "document" in data:
        node_data = data["document"]
    elif "nodes" in data:
        nodes = data["nodes"]
        first_key = next(iter(nodes))
        node_data = nodes[first_key].get("document", nodes[first_key])
    else:
        node_data = data

    node = FigmaNode(node_data)

    # Generate code
    generator_cls = GENERATORS[args.framework]
    generator = generator_cls()

    if args.framework in ("react", "vue", "svelte", "react-native", "flutter"):
        result = generator.generate(node, component_name=args.name)
    else:
        result = generator.generate(node)

    # Write output
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(result, encoding="utf-8")
        print(f"Code written to {args.output} ({args.framework})", file=sys.stderr)
    else:
        print(result)


if __name__ == "__main__":
    main()
