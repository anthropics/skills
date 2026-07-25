#!/usr/bin/env python3
"""Template-only Python plotting script."""

from __future__ import annotations

from pathlib import Path


def main() -> int:
    package_dir = Path(__file__).resolve().parent
    svg = package_dir / "figure.svg"
    svg.write_text(
        """<svg xmlns="http://www.w3.org/2000/svg" width="600" height="360" viewBox="0 0 600 360">
<rect width="600" height="360" fill="#ffffff"/>
<text x="30" y="45" font-family="Arial" font-size="18" font-weight="bold">Template-only materials figure</text>
<rect x="60" y="90" width="120" height="180" fill="#6aa5b8"/>
<rect x="230" y="140" width="120" height="130" fill="#d29f5d"/>
<rect x="400" y="110" width="120" height="160" fill="#7a9b76"/>
<text x="60" y="305" font-family="Arial" font-size="13">Replace with source data</text>
<text x="60" y="330" font-family="Arial" font-size="11">template only; not manuscript evidence</text>
</svg>
""",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
