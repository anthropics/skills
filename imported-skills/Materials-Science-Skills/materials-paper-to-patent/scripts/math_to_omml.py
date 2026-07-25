#!/usr/bin/env python3
"""Convert simple LaTeX/math ASCII into OMML (Office MathML) for DOCX insertion.

Scope: lowercase identifiers, +, -, *, /, ^, _, fractions, superscripts, subscripts.
Output: an `<m:oMath>...</m:oMath>` XML fragment. Full LaTeX coverage is out
of scope for this skill; fallback returns an empty string and the caller should
render plain text instead.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


def _identifier(text: str) -> str:
    return (
        f'<m:r><m:rPr><m:sty m:val="p"/></m:rPr><m:t xml:space="preserve">'
        f"{text}</m:t></m:r>"
    )


def _text_run(text: str) -> str:
    safe = (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )
    return f'<m:r><m:t xml:space="preserve">{safe}</m:t></m:r>'


def _sup(child: str) -> str:
    return f'<m:sSup><m:e>{child}</m:e><m:sup>{_text_run("")}</m:sup></m:sSup>'


def _sub(child: str) -> str:
    return f'<m:sSub><m:e>{child}</m:e><m:sub>{_text_run("")}</m:sub></m:sSub>'


def _frac(num: str, den: str) -> str:
    return f'<m:f><m:num>{num}</m:num><m:den>{den}</m:den></m:f>'


def render_omml(latex: str) -> str:
    """Best-effort LaTeX -> OMML. Returns "" when unable to render."""
    if not latex or not latex.strip():
        return ""
    if any(ch in latex for ch in "[]{}"):
        return ""

    body = _text_run(latex)
    body = re.sub(
        r"([A-Za-z0-9])\s*\^\s*\{?([A-Za-z0-9\-+/]+)\}?",
        lambda m: _sup(_identifier(m.group(2))),
        body,
    )
    body = re.sub(
        r"([A-Za-z0-9])\s*_\s*\{?([A-Za-z0-9\-+/]+)\}?",
        lambda m: _sub(_identifier(m.group(2))),
        body,
    )
    frac_pattern = re.compile(r"\\frac\{([^{}]+)\}\{([^{}]+)\}")
    while frac_pattern.search(body):
        body = frac_pattern.sub(lambda m: _frac(_identifier(m.group(1)), _identifier(m.group(2))), body)
    return f'<m:oMath xmlns:m="http://schemas.openxmlformats.org/officeDocument/2006/math">{body}</m:oMath>'


def latex_to_omml(latex: str) -> str:
    """Backward-compatible alias used by render_patent_docx."""
    return render_omml(latex)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="UTF-8 file containing LaTeX")
    parser.add_argument("--output", type=Path, help="Write OMML to file; default stdout")
    args = parser.parse_args()
    if not args.input.exists():
        print(f"ERROR: input not found: {args.input}", file=sys.stderr)
        return 2
    omml = render_omml(args.input.read_text(encoding="utf-8"))
    if not omml:
        print("WARN: input too complex; returning empty OMML", file=sys.stderr)
        return 1
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(omml, encoding="utf-8")
    else:
        sys.stdout.write(omml)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
