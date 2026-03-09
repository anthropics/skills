import {
  Document,
  Packer,
  Paragraph,
  TextRun,
  AlignmentType,
  HeadingLevel,
  Header,
  Footer,
  PageNumber,
  convertInchesToTwip,
} from "docx";
import { CaseData, DocumentDraft } from "../types";

export const generateDocx = async (caseData: CaseData, docDraft: DocumentDraft): Promise<Blob> => {
  // Styles
  const bodyFont = "Times New Roman"; // Federal standard
  const headingFont = "Times New Roman";
  const bodySize = 24; // 12pt
  
  // --- CAPTION ---
  const captionParagraphs = [
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [
        new TextRun({
            text: caseData.caseInfo.courtName.toUpperCase(),
            bold: true,
            font: headingFont,
            size: bodySize,
        }),
        new TextRun({
            text: `\n${caseData.caseInfo.jurisdiction.toUpperCase()}`,
            font: headingFont,
            size: bodySize,
            break: 1,
        }),
      ],
      spacing: { after: 400 }
    }),
    
    // Simple Caption Table Simulation via Tabs/Spacing (Keeping it simple for logic)
    // Real pro se caption usually has box drawing or specific formatting
    new Paragraph({
        children: [
            new TextRun({
                text: `${caseData.partyInfo.nameCaps},`,
                bold: true,
                font: bodyFont,
                size: bodySize,
            }),
            new TextRun({
                text: `\n      ${caseData.partyInfo.role},`,
                font: bodyFont,
                size: bodySize,
            }),
            new TextRun({
                text: "\n\nv.",
                font: bodyFont,
                size: bodySize,
                break: 2,
            }),
            new TextRun({
                text: `\n\n${caseData.defendants.map(d => d.name.toUpperCase()).join('; ')},`,
                bold: true,
                font: bodyFont,
                size: bodySize,
                break: 2,
            }),
            new TextRun({
                text: "\n      Defendants.",
                font: bodyFont,
                size: bodySize,
            }),
            // Case No side
            new TextRun({
                text: `\t\tCase No.: ${caseData.caseInfo.caseNumber}`,
                font: bodyFont,
                size: bodySize,
            }),
            new TextRun({
                text: `\n\t\t${docDraft.title.toUpperCase()}`,
                bold: true,
                font: bodyFont,
                size: bodySize,
            }),
        ],
        tabStops: [
            { position: 8000, type: "left" }
        ],
        spacing: { after: 400 }
    })
  ];

  // --- CONTENT ---
  const contentParagraphs = docDraft.sections.flatMap(section => [
    new Paragraph({
      text: section.heading.toUpperCase(),
      heading: HeadingLevel.HEADING_2,
      alignment: AlignmentType.CENTER,
      spacing: { before: 240, after: 120 },
      run: {
          font: headingFont,
          size: bodySize,
          bold: true,
      }
    }),
    new Paragraph({
      children: [new TextRun({
          text: section.content,
          font: bodyFont,
          size: bodySize,
      })],
      spacing: { line: 480 }, // Double spacing (240 * 2)
      indent: { firstLine: 720 }, // 0.5 inch
      alignment: AlignmentType.JUSTIFIED,
    })
  ]);

  // --- SIGNATURE ---
  const signatureParagraphs = [
    new Paragraph({
      text: `\nDated: ${new Date().toLocaleDateString()}`,
      spacing: { before: 400 },
      run: { font: bodyFont, size: bodySize }
    }),
    new Paragraph({
      text: "\nRespectfully submitted,",
      spacing: { before: 200 },
      run: { font: bodyFont, size: bodySize }
    }),
    new Paragraph({
      text: `\n\n__________________________`,
      run: { font: bodyFont, size: bodySize }
    }),
    new Paragraph({
      text: caseData.partyInfo.name,
      run: { font: bodyFont, size: bodySize }
    }),
    new Paragraph({
      text: "Pro Se Litigant",
      run: { font: bodyFont, size: bodySize }
    }),
    new Paragraph({
        text: caseData.partyInfo.addressLine1,
        run: { font: bodyFont, size: bodySize }
      }),
    new Paragraph({
        text: caseData.partyInfo.cityStateZip,
        run: { font: bodyFont, size: bodySize }
      }),
     new Paragraph({
        text: caseData.partyInfo.phone,
        run: { font: bodyFont, size: bodySize }
      }),
     new Paragraph({
        text: caseData.partyInfo.email,
        run: { font: bodyFont, size: bodySize }
      })
  ];

  const doc = new Document({
    sections: [
      {
        properties: {
          page: {
            margin: {
              top: convertInchesToTwip(1),
              bottom: convertInchesToTwip(1),
              left: convertInchesToTwip(1),
              right: convertInchesToTwip(1),
            },
          },
        },
        headers: {
            default: new Header({
                children: [
                    new Paragraph({
                        children: [
                            new TextRun({
                                children: [PageNumber.CURRENT],
                            }),
                            new TextRun({
                                text: ` - ${docDraft.title}`,
                            }),
                        ],
                        alignment: AlignmentType.RIGHT,
                    }),
                ],
            }),
        },
        children: [
          ...captionParagraphs,
          ...contentParagraphs,
          ...signatureParagraphs
        ],
      },
    ],
  });

  return await Packer.toBlob(doc);
};
