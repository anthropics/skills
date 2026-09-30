#!/usr/bin/env python3
"""
Render a Mermaid diagram to an image (PNG/SVG/PDF).

This is a thin, dependency-light wrapper around the Mermaid CLI
(`@mermaid-js/mermaid-cli`, command name `mmdc`). The validator (validate.py)
has no dependencies and always runs; rendering is the *optional* step that
needs the CLI.

Usage:
    python3 render.py diagram.mmd                 # -> diagram.png
    python3 render.py diagram.mmd -o out.svg      # explicit output / format
    python3 render.py diagram.mmd -t dark -b transparent

Install the CLI (one-time) if it is missing:
    npm install -g @mermaid-js/mermaid-cli
    # or run without installing:  npx -p @mermaid-js/mermaid-cli mmdc ...

Exit codes:
    0  rendered successfully
    1  render failed
    2  CLI not found / usage error
"""

import argparse
import os
import shutil
import subprocess
import sys


def _find_cli():
    """Return an argv prefix that invokes mmdc, or None if unavailable."""
    if shutil.which("mmdc"):
        return ["mmdc"]
    if shutil.which("npx"):
        # npx can fetch the package on demand; -y avoids the install prompt.
        return ["npx", "-y", "-p", "@mermaid-js/mermaid-cli", "mmdc"]
    return None


def main(argv=None):
    parser = argparse.ArgumentParser(description="Render a Mermaid diagram to an image.")
    parser.add_argument("input", help="Path to the .mmd source file.")
    parser.add_argument("-o", "--output",
                        help="Output file. Extension sets the format "
                             "(.png/.svg/.pdf). Defaults to <input>.png.")
    parser.add_argument("-t", "--theme", default="default",
                        choices=["default", "dark", "forest", "neutral"],
                        help="Mermaid theme (default: default).")
    parser.add_argument("-b", "--background", default="white",
                        help="Background color or 'transparent' (default: white).")
    parser.add_argument("-s", "--scale", default="2",
                        help="Output scale factor for crisp PNGs (default: 2).")
    args = parser.parse_args(argv)

    if not os.path.isfile(args.input):
        print(f"error: input not found: {args.input}", file=sys.stderr)
        return 2

    output = args.output or (os.path.splitext(args.input)[0] + ".png")

    cli = _find_cli()
    if cli is None:
        print(
            "error: Mermaid CLI (mmdc) not found.\n"
            "  Validation works without it, but rendering needs the CLI.\n"
            "  Install:  npm install -g @mermaid-js/mermaid-cli\n"
            "  Or run:   npx -p @mermaid-js/mermaid-cli mmdc -i {inp} -o {out}".format(
                inp=args.input, out=output),
            file=sys.stderr,
        )
        return 2

    cmd = cli + [
        "-i", args.input,
        "-o", output,
        "-t", args.theme,
        "-b", args.background,
        "-s", str(args.scale),
    ]

    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError as exc:
        print(f"error: render failed (exit {exc.returncode}). "
              "Run validate.py first to catch syntax issues.", file=sys.stderr)
        return 1

    print(f"Rendered: {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
