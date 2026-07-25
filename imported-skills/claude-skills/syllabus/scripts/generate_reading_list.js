#!/usr/bin/env node
/**
 * generate_reading_list.js — Bundled DOCX generator for syllabus skill.
 *
 * Accepts JSON input + output path as CLI args. Produces a clean professional
 * .docx reading list with title page, learning outcomes, sections of papers
 * (each with hyperlinked title + audience-calibrated summary + Bloom-tied
 * discussion question), and footer.
 *
 * Path-B build: this is the bundled mechanical layout logic. The skill
 * orchestrator constructs JSON; this script assembles the DOCX. ~300 lines.
 *
 * Handles `docx` package require with multi-location fallback (works whether
 * `docx` is installed locally, globally, or in a parent dir).
 *
 * JSON schema (documented in SKILL.md):
 *   { courseTitle, courseSubtitle, generatedDate, yearRange, introText,
 *     learningOutcomes: [], sections: [{ heading, papers: [...] }],
 *     auditLog: { totalQueriesSent, totalPapersReceived, totalPapersCited,
 *                  toolConstraints, searchDetails: [], failures: [] } }
 *
 * Usage:
 *   node generate_reading_list.js --input data.json --output result.docx
 */

'use strict';

const fs = require('fs');
const path = require('path');

// Multi-location require for docx package
function loadDocx() {
  const candidates = [
    'docx',                                           // Local node_modules
    path.join(process.cwd(), 'node_modules', 'docx'), // Explicit local
    '/usr/lib/node_modules/docx',                     // Global Linux
    '/usr/local/lib/node_modules/docx',               // Global macOS / brew
    path.join(process.env.HOME || '', '.npm-global', 'lib', 'node_modules', 'docx'),
  ];
  for (const candidate of candidates) {
    try {
      return require(candidate);
    } catch (e) {
      // try next
    }
  }
  console.error('error: cannot find `docx` npm package. Install with: npm install docx');
  process.exit(2);
}

const docx = loadDocx();
const {
  Document, Paragraph, TextRun, Packer, AlignmentType, HeadingLevel,
  ExternalHyperlink, Table, TableRow, TableCell, WidthType, ShadingType,
  LevelFormat, Footer, Header, PageNumber, PageBreak, BorderStyle,
} = docx;


// ----------------------------------------------------------------------------
// CLI args
// ----------------------------------------------------------------------------
function parseArgs() {
  const args = process.argv.slice(2);
  const opts = {};
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--input') opts.input = args[++i];
    else if (args[i] === '--output') opts.output = args[++i];
    else if (args[i] === '--help' || args[i] === '-h') {
      console.log('Usage: node generate_reading_list.js --input <data.json> --output <result.docx>');
      process.exit(0);
    }
  }
  if (!opts.input || !opts.output) {
    console.error('error: both --input and --output are required');
    console.error('Usage: node generate_reading_list.js --input <data.json> --output <result.docx>');
    process.exit(2);
  }
  return opts;
}


// ----------------------------------------------------------------------------
// Input validation
// ----------------------------------------------------------------------------
function validateInput(data) {
  const required = ['courseTitle', 'sections'];
  for (const field of required) {
    if (!data[field]) {
      console.error(`error: missing required field '${field}' in input JSON`);
      process.exit(2);
    }
  }
  if (!Array.isArray(data.sections) || data.sections.length === 0) {
    console.error('error: sections must be a non-empty array');
    process.exit(2);
  }
  for (const section of data.sections) {
    if (!section.heading || !Array.isArray(section.papers)) {
      console.error('error: each section must have heading + papers array');
      process.exit(2);
    }
    for (const paper of section.papers) {
      if (!paper.title || !paper.url) {
        console.error('error: each paper must have title + url');
        process.exit(2);
      }
    }
  }
}


// ----------------------------------------------------------------------------
// DOCX building blocks
// ----------------------------------------------------------------------------
const NAVY = '1A3A5C';
const LIGHT_BLUE = 'E8F0F8';
const ACCENT_BLUE = '2E5C8A';
const GRAY = '808080';
const DARK_GRAY = '404040';

function buildTitlePage(data) {
  return [
    new Paragraph({
      children: [new TextRun({ text: data.courseTitle, bold: true, size: 48, color: NAVY })],
      alignment: AlignmentType.CENTER,
      spacing: { before: 2400, after: 200 },
    }),
    new Paragraph({
      children: [new TextRun({ text: 'Supplementary Reading List', bold: false, size: 28, color: ACCENT_BLUE })],
      alignment: AlignmentType.CENTER,
      spacing: { after: 200 },
    }),
    data.courseSubtitle ? new Paragraph({
      children: [new TextRun({ text: data.courseSubtitle, italics: true, size: 22, color: DARK_GRAY })],
      alignment: AlignmentType.CENTER,
      spacing: { after: 800 },
    }) : null,
    new Paragraph({
      children: [new TextRun({ text: `Generated: ${data.generatedDate || new Date().toISOString().split('T')[0]}`, size: 18, color: GRAY })],
      alignment: AlignmentType.CENTER,
      spacing: { after: 100 },
    }),
    new Paragraph({
      children: [new TextRun({ text: `Year range: ${data.yearRange || 'last 2 years'}`, size: 18, color: GRAY })],
      alignment: AlignmentType.CENTER,
      spacing: { after: 200 },
    }),
    new Paragraph({ children: [new PageBreak()] }),
  ].filter(Boolean);
}

function buildIntroSection(data) {
  const introText = data.introText || 'This supplementary reading list collects recent peer-reviewed research relevant to each section of the course. Each entry includes a plain-language summary calibrated to the course audience and a discussion question tied to the course learning outcomes.';
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: 'Introduction', color: NAVY, bold: true, size: 32 })],
      spacing: { after: 200 },
    }),
    new Paragraph({
      children: [new TextRun({ text: introText, size: 22 })],
      spacing: { after: 200 },
    }),
    new Paragraph({
      children: [
        new TextRun({ text: 'Papers sourced via ', size: 20 }),
        new ExternalHyperlink({
          link: 'https://consensus.app',
          children: [new TextRun({ text: 'Consensus', style: 'Hyperlink', size: 20 })],
        }),
        new TextRun({ text: ' academic search. URLs in this document link directly to Consensus paper records.', size: 20 }),
      ],
      spacing: { after: 400 },
    }),
  ];
}

function buildLearningOutcomesBox(outcomes) {
  if (!outcomes || outcomes.length === 0) return [];
  const cells = [
    new TableRow({
      children: [
        new TableCell({
          width: { size: 9000, type: WidthType.DXA },
          shading: { type: ShadingType.CLEAR, color: 'auto', fill: LIGHT_BLUE },
          children: [
            new Paragraph({
              children: [new TextRun({ text: 'Course Learning Outcomes', bold: true, size: 24, color: NAVY })],
              spacing: { after: 100 },
            }),
            ...outcomes.map(outcome => new Paragraph({
              children: [new TextRun({ text: '• ' + outcome, size: 20 })],
              spacing: { after: 60 },
            })),
          ],
        }),
      ],
    }),
  ];
  return [
    new Table({
      columnWidths: [9000],
      rows: cells,
    }),
    new Paragraph({ children: [new TextRun({ text: '', size: 4 })], spacing: { after: 400 } }),
  ];
}

function buildSection(section, sectionIndex) {
  const elements = [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: `${sectionIndex}. ${section.heading}`, color: NAVY, bold: true, size: 28 })],
      spacing: { before: 400, after: 200 },
    }),
  ];
  for (let i = 0; i < section.papers.length; i++) {
    const paper = section.papers[i];
    const paperNum = `${sectionIndex}.${i + 1}`;
    // Title (hyperlinked)
    elements.push(new Paragraph({
      children: [
        new TextRun({ text: `${paperNum}. `, bold: true, size: 22 }),
        new ExternalHyperlink({
          link: paper.url,
          children: [new TextRun({ text: paper.title, style: 'Hyperlink', size: 22, bold: true })],
        }),
      ],
      spacing: { after: 60 },
    }));
    // Author / journal / year (italic gray)
    const meta = `${paper.authors || ''}${paper.journal ? ' • ' + paper.journal : ''}${paper.year ? ' (' + paper.year + ')' : ''}`;
    if (meta.trim()) {
      elements.push(new Paragraph({
        children: [new TextRun({ text: meta, italics: true, size: 18, color: GRAY })],
        spacing: { after: 60 },
      }));
    }
    // Summary
    if (paper.summary) {
      elements.push(new Paragraph({
        children: [
          new TextRun({ text: 'Summary: ', bold: true, size: 20 }),
          new TextRun({ text: paper.summary, size: 20 }),
        ],
        spacing: { after: 60 },
      }));
    }
    // Discussion question (blue accent)
    if (paper.question) {
      elements.push(new Paragraph({
        children: [
          new TextRun({ text: 'Discussion: ', bold: true, size: 20, color: ACCENT_BLUE }),
          new TextRun({ text: paper.question, size: 20 }),
        ],
        spacing: { after: 200 },
      }));
    }
  }
  return elements;
}

function buildAuditLogSection(audit) {
  if (!audit) return [];
  const elements = [
    new Paragraph({ children: [new PageBreak()] }),
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: 'Audit Log', color: NAVY, bold: true, size: 28 })],
      spacing: { after: 200 },
    }),
    new Paragraph({
      children: [
        new TextRun({ text: `Total queries sent: `, bold: true, size: 20 }),
        new TextRun({ text: `${audit.totalQueriesSent || 0}`, size: 20 }),
      ],
      spacing: { after: 60 },
    }),
    new Paragraph({
      children: [
        new TextRun({ text: `Total papers received: `, bold: true, size: 20 }),
        new TextRun({ text: `${audit.totalPapersReceived || 0}`, size: 20 }),
      ],
      spacing: { after: 60 },
    }),
    new Paragraph({
      children: [
        new TextRun({ text: `Total papers cited in this list: `, bold: true, size: 20 }),
        new TextRun({ text: `${audit.totalPapersCited || 0}`, size: 20 }),
      ],
      spacing: { after: 200 },
    }),
  ];
  if (audit.toolConstraints) {
    elements.push(new Paragraph({
      children: [
        new TextRun({ text: 'Tool constraints: ', bold: true, size: 20 }),
        new TextRun({ text: audit.toolConstraints, size: 20 }),
      ],
      spacing: { after: 200 },
    }));
  }
  if (Array.isArray(audit.searchDetails) && audit.searchDetails.length > 0) {
    elements.push(new Paragraph({
      children: [new TextRun({ text: 'Per-search detail:', bold: true, size: 22, color: NAVY })],
      spacing: { after: 100 },
    }));
    for (const sd of audit.searchDetails) {
      elements.push(new Paragraph({
        children: [
          new TextRun({ text: `• ${sd.section || 'Unassigned'}: `, bold: true, size: 18 }),
          new TextRun({ text: `"${sd.query}" → ${sd.papersReturned || 0} returned, ${sd.papersSelected || 0} selected (${sd.status || 'OK'})`, size: 18 }),
        ],
        spacing: { after: 40 },
      }));
    }
  }
  if (Array.isArray(audit.failures) && audit.failures.length > 0) {
    elements.push(new Paragraph({
      children: [new TextRun({ text: 'Failures:', bold: true, size: 22, color: 'AA0000' })],
      spacing: { before: 200, after: 100 },
    }));
    for (const f of audit.failures) {
      elements.push(new Paragraph({
        children: [new TextRun({ text: `• ${f}`, size: 18, color: '880000' })],
        spacing: { after: 40 },
      }));
    }
  }
  return elements;
}

function buildFooter(data) {
  return new Footer({
    children: [
      new Paragraph({
        children: [new TextRun({ text: `${data.courseTitle} — Supplementary Reading List`, size: 16, color: GRAY })],
        alignment: AlignmentType.CENTER,
      }),
    ],
  });
}


// ----------------------------------------------------------------------------
// Main
// ----------------------------------------------------------------------------
function main() {
  const opts = parseArgs();
  let data;
  try {
    data = JSON.parse(fs.readFileSync(opts.input, 'utf-8'));
  } catch (e) {
    console.error(`error: cannot read input JSON ${opts.input}: ${e.message}`);
    process.exit(2);
  }

  validateInput(data);

  const sections = data.sections.map((s, i) => buildSection(s, i + 1)).flat();

  const doc = new Document({
    creator: 'syllabus skill',
    title: `${data.courseTitle} — Supplementary Reading List`,
    description: 'Generated by syllabus skill via bundled generate_reading_list.js',
    sections: [
      {
        properties: {
          page: {
            margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 }, // 1 inch
            size: { width: 12240, height: 15840 }, // US Letter
          },
        },
        footers: { default: buildFooter(data) },
        children: [
          ...buildTitlePage(data),
          ...buildIntroSection(data),
          ...buildLearningOutcomesBox(data.learningOutcomes),
          ...sections,
          ...buildAuditLogSection(data.auditLog),
        ],
      },
    ],
  });

  Packer.toBuffer(doc).then(buffer => {
    fs.writeFileSync(opts.output, buffer);
    console.log(`Generated: ${opts.output} (${buffer.length} bytes, ${data.sections.length} sections, ${data.sections.reduce((sum, s) => sum + s.papers.length, 0)} papers)`);
  }).catch(e => {
    console.error(`error: DOCX packing failed: ${e.message}`);
    process.exit(2);
  });
}

main();
