#!/usr/bin/env node

// generate_reading_list.js
// Generates a professionally formatted .docx reading list from a JSON data file.
//
// Usage:
//   node generate_reading_list.js <input.json> <output.docx>
//
// The input JSON should have this shape:
// {
//   "courseTitle": "Course Name",
//   "courseSubtitle": "Optional subtitle",
//   "generatedDate": "March 17, 2026",
//   "yearRange": "2025-2026",
//   "introText": "Introductory paragraph...",
//   "learningOutcomes": ["Outcome 1", "Outcome 2"],
//   "sections": [
//     {
//       "heading": "Section Title",
//       "papers": [
//         {
//           "title": "Paper Title",
//           "authors": "Author A., Author B.",
//           "journal": "Journal Name",
//           "year": 2025,
//           "url": "https://consensus.app/papers/details/...",
//           "summary": "One-sentence summary.",
//           "question": "Discussion question."
//         }
//       ]
//     }
//   ]
// }

const fs = require('fs');
const path = require('path');

// Try to require docx from multiple locations
let docx;
try {
  docx = require('docx');
} catch (e) {
  // Try the skill's parent directory
  try {
    docx = require(path.join(__dirname, '..', 'node_modules', 'docx'));
  } catch (e2) {
    // Try the working directory
    try {
      docx = require(path.join(process.cwd(), 'node_modules', 'docx'));
    } catch (e3) {
      console.error('Error: "docx" package not found. Run "npm install docx" first.');
      process.exit(1);
    }
  }
}

const {
  Document, Packer, Paragraph, TextRun, ExternalHyperlink,
  HeadingLevel, AlignmentType, BorderStyle, LevelFormat,
  Table, TableRow, TableCell, WidthType, ShadingType
} = docx;

// -- Parse CLI arguments --
const args = process.argv.slice(2);
if (args.length < 2) {
  console.error('Usage: node generate_reading_list.js <input.json> <output.docx>');
  process.exit(1);
}

const inputPath = args[0];
const outputPath = args[1];

// -- Read and validate input JSON --
let data;
try {
  data = JSON.parse(fs.readFileSync(inputPath, 'utf-8'));
} catch (e) {
  console.error(`Error reading input JSON: ${e.message}`);
  process.exit(1);
}

if (!data.sections || !Array.isArray(data.sections)) {
  console.error('Error: input JSON must contain a "sections" array.');
  process.exit(1);
}

// -- Build the document --
async function generateDoc() {
  const children = [];

  // ===== TITLE BLOCK =====
  children.push(
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { after: 80 },
      children: [new TextRun({
        text: data.courseTitle || "Course Reading List",
        size: 36, bold: true, font: "Arial"
      })],
    })
  );

  if (data.courseSubtitle) {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { after: 80 },
        children: [new TextRun({
          text: data.courseSubtitle,
          size: 28, bold: true, font: "Arial", color: "333333"
        })],
      })
    );
  }

  children.push(
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { after: 200 },
      children: [new TextRun({
        text: `Supplementary Reading List: Recent Research (${data.yearRange || "2025"})`,
        size: 24, font: "Arial", color: "555555"
      })],
    })
  );

  // ===== INTRO TEXT =====
  const introText = data.introText ||
    "This reading list was curated using Consensus (consensus.app), an AI-powered academic search engine that indexes over 200 million peer-reviewed papers. Papers were selected for their relevance to course topics and recency. Click any paper title to view it on Consensus.";

  children.push(
    new Paragraph({
      spacing: { after: 200 },
      children: [
        new TextRun({ text: introText, size: 22, font: "Arial" }),
      ],
    })
  );

  // ===== LEARNING OUTCOMES (if provided) =====
  if (data.learningOutcomes && data.learningOutcomes.length > 0) {
    children.push(
      new Paragraph({
        spacing: { before: 200, after: 120 },
        children: [new TextRun({
          text: "Course Learning Outcomes",
          size: 24, bold: true, font: "Arial", color: "1F4E79"
        })],
      })
    );

    for (const outcome of data.learningOutcomes) {
      children.push(
        new Paragraph({
          spacing: { after: 60 },
          indent: { left: 360 },
          numbering: { reference: "outcomes", level: 0 },
          children: [new TextRun({ text: outcome, size: 20, font: "Arial" })],
        })
      );
    }

    children.push(
      new Paragraph({ spacing: { after: 200 }, children: [] })
    );
  }

  // ===== DIVIDER =====
  children.push(
    new Paragraph({
      border: { bottom: { style: BorderStyle.SINGLE, size: 6, color: "2E75B6", space: 1 } },
      spacing: { after: 300 },
      children: [],
    })
  );

  // ===== PAPER SECTIONS =====
  let paperNum = 1;

  for (const section of data.sections) {
    // Section heading
    children.push(
      new Paragraph({
        heading: HeadingLevel.HEADING_1,
        spacing: { before: 360, after: 200 },
        children: [new TextRun({
          text: section.heading,
          size: 28, bold: true, font: "Arial", color: "1F4E79"
        })],
      })
    );

    for (const paper of section.papers) {
      // Paper number + clickable title
      children.push(
        new Paragraph({
          spacing: { before: 240, after: 60 },
          children: [
            new TextRun({ text: `${paperNum}. `, size: 22, bold: true, font: "Arial" }),
            new ExternalHyperlink({
              children: [new TextRun({
                text: paper.title,
                style: "Hyperlink", size: 22, bold: true, font: "Arial"
              })],
              link: paper.url,
            }),
          ],
        })
      );

      // Authors | Journal (Year)
      children.push(
        new Paragraph({
          spacing: { after: 60 },
          indent: { left: 360 },
          children: [
            new TextRun({
              text: paper.authors,
              size: 20, font: "Arial", italics: true, color: "666666"
            }),
            new TextRun({
              text: ` | ${paper.journal} (${paper.year})`,
              size: 20, font: "Arial", color: "666666"
            }),
          ],
        })
      );

      // Summary
      if (paper.summary) {
        children.push(
          new Paragraph({
            spacing: { after: 60 },
            indent: { left: 360 },
            children: [
              new TextRun({
                text: "Summary: ",
                size: 20, bold: true, font: "Arial", color: "1F4E79"
              }),
              new TextRun({ text: paper.summary, size: 20, font: "Arial" }),
            ],
          })
        );
      }

      // Discussion Question
      if (paper.question) {
        children.push(
          new Paragraph({
            spacing: { after: 120 },
            indent: { left: 360 },
            children: [
              new TextRun({
                text: "Discussion Question: ",
                size: 20, bold: true, font: "Arial", color: "2E75B6"
              }),
              new TextRun({
                text: paper.question,
                size: 20, font: "Arial", italics: true, color: "2E75B6"
              }),
            ],
          })
        );
      }

      paperNum++;
    }
  }

  // ===== FOOTER =====
  children.push(
    new Paragraph({
      border: { top: { style: BorderStyle.SINGLE, size: 6, color: "2E75B6", space: 1 } },
      spacing: { before: 400, after: 200 },
      children: [],
    }),
    new Paragraph({
      spacing: { after: 100 },
      children: [
        new TextRun({
          text: `Generated on ${data.generatedDate || new Date().toLocaleDateString('en-US', { year: 'numeric', month: 'long', day: 'numeric' })} using `,
          size: 18, font: "Arial", color: "888888", italics: true
        }),
        new ExternalHyperlink({
          children: [new TextRun({
            text: "Consensus",
            style: "Hyperlink", size: 18, font: "Arial", italics: true
          })],
          link: "https://consensus.app",
        }),
        new TextRun({
          text: ` (consensus.app). Papers sourced from 200M+ peer-reviewed articles. ${data.footerNote || "This list is intended as a supplement to required course materials."}`,
          size: 18, font: "Arial", color: "888888", italics: true
        }),
      ],
    })
  );

  // ===== ASSEMBLE DOCUMENT =====
  const doc = new Document({
    styles: {
      default: {
        document: { run: { font: "Arial", size: 22 } },
      },
      paragraphStyles: [
        {
          id: "Heading1", name: "Heading 1",
          basedOn: "Normal", next: "Normal", quickFormat: true,
          run: { size: 28, bold: true, font: "Arial", color: "1F4E79" },
          paragraph: { spacing: { before: 360, after: 200 }, outlineLevel: 0 },
        },
      ],
    },
    numbering: {
      config: [
        {
          reference: "outcomes",
          levels: [{
            level: 0,
            format: LevelFormat.DECIMAL,
            text: "%1.",
            alignment: AlignmentType.LEFT,
            style: { paragraph: { indent: { left: 720, hanging: 360 } } }
          }]
        },
      ]
    },
    sections: [{
      properties: {
        page: {
          size: { width: 12240, height: 15840 },
          margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 },
        },
      },
      children: children,
    }],
  });

  const buffer = await Packer.toBuffer(doc);

  // Ensure the output directory exists
  const outDir = path.dirname(outputPath);
  if (!fs.existsSync(outDir)) {
    fs.mkdirSync(outDir, { recursive: true });
  }

  fs.writeFileSync(outputPath, buffer);
  console.log(`Reading list generated: ${outputPath}`);
  console.log(`Total papers: ${paperNum - 1}`);
  console.log(`Total sections: ${data.sections.length}`);
}

generateDoc().catch(err => {
  console.error(`Error generating document: ${err.message}`);
  process.exit(1);
});
