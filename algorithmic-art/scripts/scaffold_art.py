#!/usr/bin/env python3
"""
Algorithmic Art Scaffolder
Creates the folder structure and empty files for a new art project.
"""

import sys
import os
import argparse
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(description="Scaffold Algorithmic Art Project")
    parser.add_argument("--name", required=True, help="Name of the art project")
    parser.add_argument("--output-dir", default="OUTBOX", help="Directory to output to")
    
    args = parser.parse_args()
    
    base_dir = Path(args.output_dir) / args.name
    base_dir.mkdir(parents=True, exist_ok=True)
    
    (base_dir / "philosophy.md").write_text("# Algorithmic Philosophy\n\nTODO: Write philosophy here.")
    (base_dir / "sketch.js").write_text("// TODO: p5.js code here")
    (base_dir / "index.html").write_text("<!-- TODO: HTML harness here -->")
    
    print(f"Scaffolded project '{args.name}' in {base_dir}")

if __name__ == "__main__":
    main()
