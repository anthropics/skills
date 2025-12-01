const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell, 
        Header, Footer, AlignmentType, BorderStyle, WidthType, 
        PageNumber, LevelFormat, ShadingType, TabStopType, TabStopPosition,
        ExternalHyperlink } = require('docx');
const fs = require('fs');

// ============================================================
// 設定データ（ここを編集してカスタマイズ）
// ============================================================
const RESUME_DATA = {
  // 基本情報
  mainTitle: "生成AI勉強会",
  subTitle: "【タイトル】業務効率化のためのClaude活用術",
  date: "2025年○月○日（○）14:00〜16:00",
  venue: "○○会議室 / オンライン（Zoom）",
  instructor: "○○ ○○（株式会社けんけん / MIRAICHI）",
  
  // 学習目標
  goals: [
    "生成AIの基本概念と活用シーンを理解する",
    "Claudeの特徴と他のAIツールとの違いを把握する",
    "実務で使えるプロンプトの書き方を身につける",
    "自社業務への適用イメージを具体化する"
  ],
  
  // タイムテーブル
  timetable: [
    { time: "14:00-14:10", content: "オープニング・自己紹介" },
    { time: "14:10-14:40", content: "生成AIの基礎知識" },
    { time: "14:40-15:10", content: "Claude活用デモンストレーション" },
    { time: "15:10-15:20", content: "休憩", isBreak: true },
    { time: "15:20-15:50", content: "ハンズオン：プロンプト実践" },
    { time: "15:50-16:00", content: "質疑応答・クロージング" }
  ],
  
  // 事前準備
  preparations: [
    "Claudeアカウントの作成（https://claude.ai）",
    "PC（Chrome推奨）またはスマートフォンの持参",
    "Wi-Fi接続環境の確認"
  ],
  
  // 参考リンク（ラベルとURLを分離）
  references: [
    { label: "Claude公式サイト", url: "https://claude.ai" },
    { label: "Anthropic公式ドキュメント", url: "https://docs.anthropic.com" },
    { label: "プロンプトエンジニアリングガイド", url: "https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering" }
  ],
  
  // ヘッダー・フッター
  headerText: "株式会社けんけん / MIRAICHI",
  footerNote: "本資料の無断複製・転載を禁じます。",
  
  // 出力設定
  outputPath: "/mnt/user-data/outputs/",
  outputFilename: "勉強会レジュメ"
};

// ============================================================
// Jony Ive Design System Colors
// ============================================================
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

// ============================================================
// 罫線スタイル定義
// ============================================================
const thinBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
const cellBorders = { top: thinBorder, bottom: thinBorder, left: thinBorder, right: thinBorder };

// ============================================================
// レジュメ生成関数
// ============================================================
function createResume(data) {
  const doc = new Document({
    styles: {
      default: { 
        document: { 
          run: { font: "メイリオ", size: 20 }
        } 
      },
      paragraphStyles: [
        { id: "Title", name: "Title", basedOn: "Normal",
          run: { size: 56, bold: true, color: COLORS.black, font: "メイリオ" },
          paragraph: { spacing: { before: 0, after: 100 }, alignment: AlignmentType.LEFT } },
        { id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal", quickFormat: true,
          run: { size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" },
          paragraph: { spacing: { before: 400, after: 120 }, outlineLevel: 0 } },
        { id: "BodyText", name: "Body Text", basedOn: "Normal",
          run: { size: 20, color: COLORS.dark_gray, font: "メイリオ" },
          paragraph: { spacing: { after: 80 } } },
        { id: "SmallText", name: "Small Text", basedOn: "Normal",
          run: { size: 18, color: COLORS.light_gray, font: "メイリオ" },
          paragraph: { spacing: { after: 40 } } }
      ]
    },
    numbering: {
      config: [
        { reference: "bullet-list",
          levels: [{ level: 0, format: LevelFormat.BULLET, text: "•", alignment: AlignmentType.LEFT,
            style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
        { reference: "numbered-list",
          levels: [{ level: 0, format: LevelFormat.DECIMAL, text: "%1.", alignment: AlignmentType.LEFT,
            style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] }
      ]
    },
    sections: [{
      properties: {
        page: {
          margin: { top: 1134, right: 1134, bottom: 1134, left: 1134 }
        }
      },
      headers: {
        default: new Header({
          children: [
            new Paragraph({
              alignment: AlignmentType.RIGHT,
              children: [
                new TextRun({ text: data.headerText, size: 16, color: COLORS.light_gray, font: "メイリオ" })
              ]
            })
          ]
        })
      },
      footers: {
        default: new Footer({
          children: [
            new Paragraph({
              alignment: AlignmentType.CENTER,
              children: [
                new TextRun({ text: "Page ", size: 16, color: COLORS.light_gray, font: "メイリオ" }),
                new TextRun({ children: [PageNumber.CURRENT], size: 16, color: COLORS.light_gray, font: "メイリオ" }),
                new TextRun({ text: " / ", size: 16, color: COLORS.light_gray, font: "メイリオ" }),
                new TextRun({ children: [PageNumber.TOTAL_PAGES], size: 16, color: COLORS.light_gray, font: "メイリオ" })
              ]
            })
          ]
        })
      },
      children: [
        // ===== タイトル（シンプルなParagraph） =====
        new Paragraph({
          spacing: { after: 100 },
          children: [
            new TextRun({ text: data.mainTitle, size: 56, bold: true, color: COLORS.black, font: "メイリオ" })
          ]
        }),
        
        // サブタイトル
        new Paragraph({
          spacing: { after: 300 },
          children: [
            new TextRun({ text: data.subTitle, size: 24, color: COLORS.medium_gray, font: "メイリオ" })
          ]
        }),
        
        // ===== 基本情報（タブで整列） =====
        new Paragraph({
          spacing: { after: 60 },
          tabStops: [{ type: TabStopType.LEFT, position: 1440 }],
          border: { bottom: { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator } },
          children: [
            new TextRun({ text: "日時", size: 20, bold: true, color: COLORS.medium_gray, font: "メイリオ" }),
            new TextRun({ text: "\t" }),
            new TextRun({ text: data.date, size: 20, color: COLORS.dark_gray, font: "メイリオ" })
          ]
        }),
        new Paragraph({
          spacing: { after: 60 },
          tabStops: [{ type: TabStopType.LEFT, position: 1440 }],
          border: { bottom: { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator } },
          children: [
            new TextRun({ text: "場所", size: 20, bold: true, color: COLORS.medium_gray, font: "メイリオ" }),
            new TextRun({ text: "\t" }),
            new TextRun({ text: data.venue, size: 20, color: COLORS.dark_gray, font: "メイリオ" })
          ]
        }),
        new Paragraph({
          spacing: { after: 60 },
          tabStops: [{ type: TabStopType.LEFT, position: 1440 }],
          border: { bottom: { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator } },
          children: [
            new TextRun({ text: "講師", size: 20, bold: true, color: COLORS.medium_gray, font: "メイリオ" }),
            new TextRun({ text: "\t" }),
            new TextRun({ text: data.instructor, size: 20, color: COLORS.dark_gray, font: "メイリオ" })
          ]
        }),
        
        // 余白
        new Paragraph({ spacing: { before: 400 }, children: [] }),
        
        // ===== 学習目標 =====
        new Paragraph({
          spacing: { before: 200, after: 120 },
          children: [new TextRun({ text: "学習目標・ゴール", size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        new Paragraph({
          spacing: { after: 80 },
          children: [new TextRun({ text: "この勉強会を通じて、以下の内容を習得することを目指します。", size: 20, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        ...data.goals.map(goal => new Paragraph({
          numbering: { reference: "bullet-list", level: 0 },
          children: [new TextRun({ text: goal, size: 20, color: COLORS.dark_gray, font: "メイリオ" })]
        })),
        
        // 余白
        new Paragraph({ spacing: { before: 200 }, children: [] }),
        
        // ===== タイムテーブル =====
        new Paragraph({
          spacing: { before: 200, after: 120 },
          children: [new TextRun({ text: "タイムテーブル", size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        createTimetableTable(data),
        
        // 余白
        new Paragraph({ spacing: { before: 200 }, children: [] }),
        
        // ===== 事前準備 =====
        new Paragraph({
          spacing: { before: 200, after: 120 },
          children: [new TextRun({ text: "事前準備事項", size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        ...data.preparations.map(prep => new Paragraph({
          numbering: { reference: "numbered-list", level: 0 },
          children: [new TextRun({ text: prep, size: 20, color: COLORS.dark_gray, font: "メイリオ" })]
        })),
        
        // 余白
        new Paragraph({ spacing: { before: 200 }, children: [] }),
        
        // ===== 参考リンク =====
        new Paragraph({
          spacing: { before: 200, after: 120 },
          children: [new TextRun({ text: "参考リンク・資料", size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        ...data.references.map(ref => new Paragraph({
          numbering: { reference: "bullet-list", level: 0 },
          children: [
            new TextRun({ text: ref.label + ": ", size: 20, color: COLORS.dark_gray, font: "メイリオ" }),
            new ExternalHyperlink({
              children: [
                new TextRun({ text: ref.url, size: 20, color: "0563C1", underline: { type: "single" }, font: "メイリオ" })
              ],
              link: ref.url
            })
          ]
        })),
        
        // 余白
        new Paragraph({ spacing: { before: 400 }, children: [] }),
        
        // ===== メモ欄 =====
        new Paragraph({
          spacing: { before: 200, after: 120 },
          children: [new TextRun({ text: "メモ欄", size: 28, bold: true, color: COLORS.dark_gray, font: "メイリオ" })]
        }),
        createMemoTable(),
        
        // フッター注記
        new Paragraph({ spacing: { before: 400 }, children: [] }),
        new Paragraph({
          alignment: AlignmentType.RIGHT,
          children: [
            new TextRun({ text: data.footerNote, size: 16, color: COLORS.light_gray, font: "メイリオ" })
          ]
        })
      ]
    }]
  });

  return doc;
}

// タイムテーブル（テーブル幅を明示的に指定）
function createTimetableTable(data) {
  const headerRow = new TableRow({
    tableHeader: true,
    children: [
      new TableCell({
        borders: cellBorders,
        width: { size: 2000, type: WidthType.DXA },
        shading: { fill: COLORS.bg_gray, type: ShadingType.CLEAR },
        children: [new Paragraph({ 
          alignment: AlignmentType.CENTER,
          children: [new TextRun({ text: "時間", size: 20, bold: true, color: COLORS.dark_gray, font: "メイリオ" })] 
        })]
      }),
      new TableCell({
        borders: cellBorders,
        width: { size: 7360, type: WidthType.DXA },
        shading: { fill: COLORS.bg_gray, type: ShadingType.CLEAR },
        children: [new Paragraph({ children: [new TextRun({ text: "内容", size: 20, bold: true, color: COLORS.dark_gray, font: "メイリオ" })] })]
      })
    ]
  });
  
  const dataRows = data.timetable.map(item => 
    new TableRow({
      children: [
        new TableCell({
          borders: cellBorders,
          width: { size: 2000, type: WidthType.DXA },
          children: [new Paragraph({ 
            alignment: AlignmentType.CENTER, 
            children: [new TextRun({ text: item.time, size: 20, color: COLORS.dark_gray, font: "メイリオ" })] 
          })]
        }),
        new TableCell({
          borders: cellBorders,
          width: { size: 7360, type: WidthType.DXA },
          children: [new Paragraph({ 
            children: [new TextRun({ 
              text: item.content, 
              size: 20, 
              color: item.isBreak ? COLORS.light_gray : COLORS.dark_gray, 
              font: "メイリオ" 
            })] 
          })]
        })
      ]
    })
  );
  
  return new Table({
    width: { size: 100, type: WidthType.PERCENTAGE },
    columnWidths: [2000, 7360],
    rows: [headerRow, ...dataRows]
  });
}

// メモ欄テーブル
function createMemoTable() {
  return new Table({
    width: { size: 100, type: WidthType.PERCENTAGE },
    columnWidths: [9360],
    rows: [
      new TableRow({
        height: { value: 3600, rule: "atLeast" },
        children: [
          new TableCell({
            borders: cellBorders,
            width: { size: 9360, type: WidthType.DXA },
            children: [
              new Paragraph({ spacing: { after: 300 }, children: [] }),
              new Paragraph({ spacing: { after: 300 }, children: [] }),
              new Paragraph({ spacing: { after: 300 }, children: [] }),
              new Paragraph({ spacing: { after: 300 }, children: [] }),
              new Paragraph({ spacing: { after: 300 }, children: [] }),
              new Paragraph({ spacing: { after: 300 }, children: [] })
            ]
          })
        ]
      })
    ]
  });
}

// ============================================================
// メイン実行
// ============================================================
const doc = createResume(RESUME_DATA);
const outputPath = `${RESUME_DATA.outputPath}${RESUME_DATA.outputFilename}.docx`;

Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync(outputPath, buffer);
  console.log(`✅ 勉強会レジュメを作成しました: ${outputPath}`);
});
