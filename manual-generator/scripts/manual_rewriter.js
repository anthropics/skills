/**
 * Manual Rewriter - 既存マニュアルを新フォーマットでリライト
 * 抽出済みJSON → 新フォーマットDOCX
 */

const {
  Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell,
  Header, Footer, AlignmentType, PageOrientation, LevelFormat,
  HeadingLevel, BorderStyle, WidthType, PageNumber, PageBreak,
  ShadingType
} = require('docx');
const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// ====================
// デザインシステム定数
// ====================
const COLORS = {
  black: "000000",
  dark_gray: "333333",
  medium_gray: "666666",
  light_gray: "999999",
  pale_gray: "CCCCCC",
  separator: "E0E0E0",
  bg_gray: "F5F5F5",
  white: "FFFFFF",
  accent: "5B7B94"
};

const FONT_NAME = "メイリオ";

// ====================
// コマンドライン引数解析
// ====================
function parseArgs() {
  const args = process.argv.slice(2);
  const config = {
    input: null,           // 入力ファイル（PDF/DOCX）または抽出済みJSON
    output: '/mnt/user-data/outputs/rewritten_manual.docx',
    type: 'system',
    industry: 'general',
    audience: 'beginner',
    version: '1.0',
    author: '',
    preserveStructure: true  // 元の構造を保持するか
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--input': config.input = args[++i]; break;
      case '--output': config.output = args[++i]; break;
      case '--type': config.type = args[++i]; break;
      case '--industry': config.industry = args[++i]; break;
      case '--audience': config.audience = args[++i]; break;
      case '--version': config.version = args[++i]; break;
      case '--author': config.author = args[++i]; break;
      case '--restructure': config.preserveStructure = false; break;
    }
  }
  return config;
}

// ====================
// スタイル定義
// ====================
function getDocumentStyles() {
  return {
    default: {
      document: {
        run: { font: FONT_NAME, size: 20 }
      }
    },
    paragraphStyles: [
      {
        id: "Title", name: "Title", basedOn: "Normal",
        run: { size: 56, bold: true, color: COLORS.black, font: FONT_NAME },
        paragraph: { spacing: { before: 400, after: 200 }, alignment: AlignmentType.CENTER }
      },
      {
        id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 32, bold: true, color: COLORS.black, font: FONT_NAME },
        paragraph: { spacing: { before: 400, after: 200 }, outlineLevel: 0 }
      },
      {
        id: "Heading2", name: "Heading 2", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 28, bold: true, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { before: 300, after: 150 }, outlineLevel: 1 }
      },
      {
        id: "Heading3", name: "Heading 3", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 24, bold: true, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { before: 200, after: 100 }, outlineLevel: 2 }
      },
      {
        id: "BodyText", name: "Body Text", basedOn: "Normal",
        run: { size: 20, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { after: 120, line: 360 } }
      }
    ]
  };
}

function getNumberingConfig() {
  return {
    config: [
      {
        reference: "bullet-list",
        levels: [{
          level: 0, format: LevelFormat.BULLET, text: "•",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } }
        }]
      },
      {
        reference: "num-list",
        levels: [{
          level: 0, format: LevelFormat.DECIMAL, text: "%1.",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } }
        }]
      }
    ]
  };
}

// ====================
// タイトル分割
// ====================
function splitTitleIntoLines(title) {
  const splitKeywords = [
    '操作マニュアル', '業務マニュアル', 'マニュアル', '手順書',
    '操作手順', 'ガイドライン', 'ガイド', '規程', '規則', '要領', 'フロー', '対応マニュアル'
  ];

  for (const keyword of splitKeywords) {
    const index = title.indexOf(keyword);
    if (index > 0) {
      return [title.substring(0, index).trim(), title.substring(index).trim()];
    }
  }

  if (title.length > 15) {
    const breakPoints = ['の', 'に関する', 'における', 'について', '用'];
    for (const bp of breakPoints) {
      const index = title.lastIndexOf(bp);
      if (index > 5 && index < title.length - 5) {
        const line1 = title.substring(0, index + bp.length).trim();
        const line2 = title.substring(index + bp.length).trim();
        if (line2.length > 0) return [line1, line2];
      }
    }
  }

  return [title];
}

// ====================
// コンテンツ変換
// ====================

/**
 * テキストコンテンツをParagraph配列に変換
 */
function contentToParagraphs(content, config) {
  if (!content || content.trim() === '') {
    return [];
  }

  const paragraphs = [];
  const lines = content.split('\n');

  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed) continue;

    // 箇条書き判定
    const bulletMatch = trimmed.match(/^[\-\*•・]\s*(.+)$/);
    if (bulletMatch) {
      paragraphs.push(
        new Paragraph({
          numbering: { reference: "bullet-list", level: 0 },
          children: [new TextRun({ text: bulletMatch[1], size: 20, font: FONT_NAME })]
        })
      );
      continue;
    }

    // 番号リスト判定
    const numMatch = trimmed.match(/^(\d+)[\.）\)]\s*(.+)$/);
    if (numMatch) {
      paragraphs.push(
        new Paragraph({
          numbering: { reference: "num-list", level: 0 },
          children: [new TextRun({ text: numMatch[2], size: 20, font: FONT_NAME })]
        })
      );
      continue;
    }

    // 通常のテキスト
    paragraphs.push(
      new Paragraph({
        style: "BodyText",
        children: [new TextRun({ text: trimmed, size: 20, font: FONT_NAME })]
      })
    );
  }

  return paragraphs;
}

/**
 * 平易化処理（協同組合向け）
 */
function simplifyText(text) {
  const replacements = [
    [/当該/g, 'この'],
    [/該当する/g, '当てはまる'],
    [/所定の/g, '決められた'],
    [/様式/g, '用紙'],
    [/申請/g, '申し込み'],
    [/記載/g, '書く'],
    [/提出/g, '出す'],
    [/確認/g, 'チェック'],
    [/実施/g, '行う'],
    [/遵守/g, '守る'],
    [/留意/g, '気をつける'],
    [/速やかに/g, 'すぐに'],
    [/適宜/g, '必要に応じて'],
  ];

  let result = text;
  for (const [pattern, replacement] of replacements) {
    result = result.replace(pattern, replacement);
  }
  return result;
}

// ====================
// セクション生成
// ====================

function generateCoverPage(title, config, metadata) {
  const titleLines = splitTitleIntoLines(title);
  const children = [
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] })
  ];

  titleLines.forEach((line, index) => {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { after: index === titleLines.length - 1 ? 400 : 100 },
        children: [new TextRun({
          text: line,
          bold: true,
          size: index === 0 ? 72 : 64,
          font: FONT_NAME,
          color: COLORS.black
        })]
      })
    );
  });

  children.push(
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { after: 200 },
      children: [new TextRun({ text: "【リライト版】", size: 24, font: FONT_NAME, color: COLORS.accent })]
    }),
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] })
  );

  // 金融機関向け機密区分
  if (config.industry === 'finance') {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { before: 400 },
        children: [new TextRun({ text: "【機密区分】", bold: true, size: 22, font: FONT_NAME })]
      }),
      new Paragraph({
        alignment: AlignmentType.CENTER,
        children: [new TextRun({ text: "□ 社外秘　□ 部外秘　□ 一般", size: 20, font: FONT_NAME })]
      })
    );
  }

  // メタ情報
  const version = metadata.version || config.version;
  const author = metadata.author || config.author || '[作成者]';

  children.push(
    new Paragraph({ children: [] }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text: `バージョン: ${version}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
    }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text: `改訂日: ${formatDate(new Date())}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
    }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text: `作成者: ${author}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
    }),
    new Paragraph({ children: [new PageBreak()] })
  );

  return children;
}

function generateSectionContent(section, config, sectionNum) {
  const children = [];
  const shouldSimplify = config.industry === 'cooperative';

  // セクション見出し
  const headingLevel = section.level === 1 ? HeadingLevel.HEADING_1 : HeadingLevel.HEADING_2;
  const prefix = section.level === 1 ? `${sectionNum}. ` : `${sectionNum}.${children.length + 1} `;
  
  children.push(
    new Paragraph({
      heading: headingLevel,
      children: [new TextRun({ text: `${prefix}${section.title}` })]
    })
  );

  // コンテンツ
  if (section.content) {
    const content = shouldSimplify ? simplifyText(section.content) : section.content;
    children.push(...contentToParagraphs(content, config));
  }

  // サブセクション
  if (section.subsections && section.subsections.length > 0) {
    section.subsections.forEach((sub, subIndex) => {
      children.push(
        new Paragraph({
          heading: HeadingLevel.HEADING_3,
          children: [new TextRun({ text: `${sectionNum}.${subIndex + 1} ${sub.title}` })]
        })
      );

      if (sub.content) {
        const content = shouldSimplify ? simplifyText(sub.content) : sub.content;
        children.push(...contentToParagraphs(content, config));
      }
    });
  }

  return children;
}

function generateRevisionHistory(config, metadata) {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  const createHeaderCell = (text) => new TableCell({
    borders: cellBorders,
    shading: { fill: COLORS.dark_gray, type: ShadingType.CLEAR },
    children: [new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text, bold: true, size: 20, font: FONT_NAME, color: COLORS.white })]
    })]
  });

  const createBodyCell = (text) => new TableCell({
    borders: cellBorders,
    children: [new Paragraph({
      children: [new TextRun({ text, size: 20, font: FONT_NAME })]
    })]
  });

  return [
    new Paragraph({ children: [new PageBreak()] }),
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "改訂履歴" })]
    }),
    new Table({
      columnWidths: [1500, 2000, 4000, 2000],
      rows: [
        new TableRow({
          tableHeader: true,
          children: [
            createHeaderCell("Ver."),
            createHeaderCell("改訂日"),
            createHeaderCell("改訂内容"),
            createHeaderCell("改訂者")
          ]
        }),
        new TableRow({
          children: [
            createBodyCell(metadata.version || "1.0"),
            createBodyCell(metadata.date || formatDate(new Date())),
            createBodyCell("原本からリライト"),
            createBodyCell(metadata.author || config.author || "[作成者]")
          ]
        }),
        new TableRow({
          children: [
            createBodyCell(config.version),
            createBodyCell(formatDate(new Date())),
            createBodyCell("新フォーマット適用"),
            createBodyCell(config.author || "[作成者]")
          ]
        })
      ]
    })
  ];
}

function formatDate(date) {
  return `${date.getFullYear()}年${date.getMonth() + 1}月${date.getDate()}日`;
}

// ====================
// ヘッダー・フッター
// ====================
function getHeader(title, version) {
  return new Header({
    children: [
      new Paragraph({
        alignment: AlignmentType.RIGHT,
        children: [
          new TextRun({ text: title, size: 18, font: FONT_NAME, color: COLORS.light_gray }),
          new TextRun({ text: `  Ver.${version}`, size: 18, font: FONT_NAME, color: COLORS.light_gray })
        ]
      })
    ]
  });
}

function getFooter() {
  return new Footer({
    children: [
      new Paragraph({
        alignment: AlignmentType.CENTER,
        children: [
          new TextRun({ text: "- ", size: 18, font: FONT_NAME, color: COLORS.light_gray }),
          new TextRun({ children: [PageNumber.CURRENT], size: 18, font: FONT_NAME, color: COLORS.light_gray }),
          new TextRun({ text: " -", size: 18, font: FONT_NAME, color: COLORS.light_gray })
        ]
      })
    ]
  });
}

// ====================
// メイン処理
// ====================
async function rewriteManual(config) {
  console.log('📝 マニュアルリライトを開始します...');

  // 入力ファイル処理
  let structureData;
  const ext = path.extname(config.input).toLowerCase();

  if (ext === '.json') {
    // 抽出済みJSON
    console.log('📄 抽出済みJSONを読み込み...');
    structureData = JSON.parse(fs.readFileSync(config.input, 'utf-8'));
  } else {
    // PDF/DOCXから抽出
    console.log('📄 ファイルからコンテンツを抽出...');
    const { extractContent } = require('./content_extractor.js');
    const tempJson = '/tmp/extracted_structure.json';
    await extractContent(config.input, tempJson);
    structureData = JSON.parse(fs.readFileSync(tempJson, 'utf-8'));
  }

  const structure = structureData.structure;
  const metadata = structure.metadata || {};
  const title = structure.title || 'マニュアル';

  console.log(`   タイトル: ${title}`);
  console.log(`   セクション数: ${structure.sections.length}`);
  console.log(`   業種: ${config.industry}`);

  // ドキュメント構成
  let allChildren = [];

  // 表紙
  allChildren = allChildren.concat(generateCoverPage(title, config, metadata));

  // 各セクション
  structure.sections.forEach((section, index) => {
    allChildren = allChildren.concat(generateSectionContent(section, config, index + 1));
  });

  // 改訂履歴
  allChildren = allChildren.concat(generateRevisionHistory(config, metadata));

  // ドキュメント生成
  const doc = new Document({
    styles: getDocumentStyles(),
    numbering: getNumberingConfig(),
    sections: [{
      properties: {
        page: {
          margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 },
          size: { orientation: PageOrientation.PORTRAIT }
        }
      },
      headers: { default: getHeader(title, config.version) },
      footers: { default: getFooter() },
      children: allChildren
    }]
  });

  // ファイル出力
  const buffer = await Packer.toBuffer(doc);
  const outputDir = path.dirname(config.output);
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
  fs.writeFileSync(config.output, buffer);

  console.log(`✅ リライト完了: ${config.output}`);
  return config.output;
}

// ====================
// CLI実行
// ====================
if (require.main === module) {
  const config = parseArgs();

  if (!config.input) {
    console.log('使用方法: node manual_rewriter.js --input <ファイル> [オプション]');
    console.log('');
    console.log('オプション:');
    console.log('  --input <file>      入力ファイル（PDF/DOCX/JSON）');
    console.log('  --output <file>     出力ファイル（デフォルト: rewritten_manual.docx）');
    console.log('  --type <type>       マニュアルタイプ（system/workflow/service）');
    console.log('  --industry <ind>    業種（general/finance/cooperative）');
    console.log('  --version <ver>     新バージョン番号');
    console.log('  --author <name>     作成者名');
    process.exit(1);
  }

  if (!fs.existsSync(config.input)) {
    console.error(`❌ ファイルが見つかりません: ${config.input}`);
    process.exit(1);
  }

  rewriteManual(config)
    .then(() => console.log('完了'))
    .catch(err => {
      console.error('エラー:', err.message);
      process.exit(1);
    });
}

module.exports = { rewriteManual };
