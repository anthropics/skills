#!/usr/bin/env python3
"""Extract a version section from CHANGELOG.md."""
from pathlib import Path
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("version", help="release version, e.g. 0.5.0")
parser.add_argument("--changelog", default="CHANGELOG.md")
args = parser.parse_args()

text = Path(args.changelog).read_text()
heading = f"## [{args.version}]"
start = text.index(heading)
next_heading = text.find("\n## [", start + len(heading))
section = text[start:] if next_heading == -1 else text[start:next_heading]
print(section.strip())
