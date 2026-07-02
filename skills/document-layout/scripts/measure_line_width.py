#!/usr/bin/env python3
"""
measure_line_width.py - Determine effective character limit per line.

Part of the document-typography skill.

Generates a test .docx with lines of known length (50-90 chars),
so you can visually determine where wrapping starts for a given
font, size, and indent combination.

Usage:
    python measure_line_width.py
    python measure_line_width.py --font "Georgia" --size 11 --indent 620
    python measure_line_width.py --font "Calibri" --size 11 --indent 720

Then run:
    node line_width_test.js
    bash check_layout.sh line_width_test.docx

Inspect the page images: the last line that fits on a single row
tells you the maximum character count for your setup.
"""

import argparse

TEMPLATE = '''
const fs = require('fs');
const {{ Document, Packer, Paragraph, TextRun }} = require('docx');

const font = "{font}";
const bodySize = {size_dxa};
const indent = {indent};

function testLine(charCount, text) {{
  return new Paragraph({{
    spacing: {{ before: 60, after: 60 }},
    indent: {{ left: indent, hanging: indent }},
    children: [
      new TextRun({{ text: charCount + ".  ", font, size: bodySize, bold: true }}),
      new TextRun({{ text: text + " [" + text.length + " chars]", font, size: bodySize }})
    ]
  }});
}}

function makeStr(n) {{
  const words = "dit is een test zin met woorden van verschillende lengte voor meting";
  let result = "";
  const arr = words.split(" ");
  let wi = 0;
  while (result.length < n) {{
    result += (result ? " " : "") + arr[wi % arr.length];
    wi++;
  }}
  return result.substring(0, n);
}}

const doc = new Document({{
  styles: {{ default: {{ document: {{ run: {{ font, size: bodySize }} }} }} }},
  sections: [{{
    properties: {{
      page: {{
        size: {{ width: 11906, height: 16838 }},
        margin: {{ top: 1440, right: 1440, bottom: 1440, left: 1440 }}
      }}
    }},
    children: [
      new Paragraph({{
        spacing: {{ after: 200 }},
        children: [new TextRun({{
          text: "Line Width Test: " + font + " " + ({size_dxa}/2) + "pt, indent " + indent + " DXA",
          font, size: bodySize + 4, bold: true
        }})]
      }}),
      new Paragraph({{
        spacing: {{ after: 200 }},
        children: [new TextRun({{
          text: "The last line that fits on ONE row = your max character count.",
          font, size: bodySize, italics: true
        }})]
      }}),
      ...Array.from({{length: 36}}, (_, i) => {{
        const len = 50 + i;
        return testLine(len, makeStr(len));
      }})
    ]
  }}]
}});

Packer.toBuffer(doc).then(buffer => {{
  fs.writeFileSync("line_width_test.docx", buffer);
  console.log("Generated line_width_test.docx");
  console.log("Run: bash check_layout.sh line_width_test.docx");
}});
'''


def main():
    parser = argparse.ArgumentParser(
        description="Generate a test document to measure effective line width"
    )
    parser.add_argument("--font", default="Georgia",
                        help="Font name (default: Georgia)")
    parser.add_argument("--size", type=int, default=11,
                        help="Font size in pt (default: 11)")
    parser.add_argument("--indent", type=int, default=620,
                        help="Hanging indent in DXA (default: 620)")
    args = parser.parse_args()

    size_dxa = args.size * 2

    script = TEMPLATE.format(
        font=args.font,
        size_dxa=size_dxa,
        indent=args.indent
    )

    with open("line_width_test.js", "w") as f:
        f.write(script)

    print(f"Generated line_width_test.js")
    print(f"  Font: {args.font} {args.size}pt")
    print(f"  Indent: {args.indent} DXA")
    print(f"")
    print(f"Next steps:")
    print(f"  node line_width_test.js")
    print(f"  bash check_layout.sh line_width_test.docx")
    print(f"  Then inspect page images to find the wrap point.")


if __name__ == "__main__":
    main()
