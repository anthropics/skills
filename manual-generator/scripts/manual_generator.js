/**
 * Manual Generator - 業務マニュアル自動生成スクリプト
 * Jony Iveデザインシステム準拠
 */

const {
  Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell,
  Header, Footer, AlignmentType, PageOrientation, LevelFormat,
  HeadingLevel, BorderStyle, WidthType, PageNumber, PageBreak,
  ImageRun, ShadingType
} = require('docx');
const fs = require('fs');
const path = require('path');

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
// 画像処理関数
// ====================

/**
 * 画像ファイルの拡張子からMIMEタイプを取得
 */
function getImageType(imagePath) {
  const ext = path.extname(imagePath).toLowerCase();
  const typeMap = {
    '.png': 'png',
    '.jpg': 'jpg',
    '.jpeg': 'jpeg',
    '.gif': 'gif',
    '.bmp': 'bmp'
  };
  return typeMap[ext] || 'png';
}

/**
 * 画像をマニュアルに埋め込むためのParagraph配列を生成
 * @param {string} imagePath - 画像ファイルパス
 * @param {string} caption - キャプション（図番号含む）
 * @param {number} maxWidth - 最大幅（ポイント）
 */
function createImageWithCaption(imagePath, caption, maxWidth = 450) {
  if (!fs.existsSync(imagePath)) {
    console.warn(`⚠️ 画像ファイルが見つかりません: ${imagePath}`);
    return [
      new Paragraph({
        alignment: AlignmentType.CENTER,
        shading: { fill: COLORS.bg_gray, type: ShadingType.CLEAR },
        children: [new TextRun({ 
          text: `[画像: ${caption}]`, 
          italics: true, 
          size: 20, 
          font: FONT_NAME,
          color: COLORS.medium_gray 
        })]
      })
    ];
  }

  const imageBuffer = fs.readFileSync(imagePath);
  const imageType = getImageType(imagePath);

  return [
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { before: 200, after: 100 },
      children: [
        new ImageRun({
          type: imageType,
          data: imageBuffer,
          transformation: { width: maxWidth, height: maxWidth * 0.6 },
          altText: { 
            title: caption, 
            description: caption, 
            name: path.basename(imagePath) 
          }
        })
      ]
    }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { after: 200 },
      children: [new TextRun({ 
        text: caption, 
        italics: true, 
        size: 18, 
        font: FONT_NAME,
        color: COLORS.medium_gray 
      })]
    })
  ];
}

/**
 * 操作手順JSONを読み込んでパース
 */
function loadStepsFromJson(jsonPath) {
  if (!jsonPath || !fs.existsSync(jsonPath)) {
    return null;
  }
  try {
    const content = fs.readFileSync(jsonPath, 'utf-8');
    return JSON.parse(content);
  } catch (e) {
    console.error(`❌ JSONパースエラー: ${e.message}`);
    return null;
  }
}

/**
 * 操作手順セクションを生成（画像付き）
 */
function generateStepsWithImages(stepsData) {
  const children = [];
  
  if (!stepsData || !stepsData.steps || stepsData.steps.length === 0) {
    return children;
  }

  stepsData.steps.forEach((step, index) => {
    const stepNum = step.number || (index + 1);
    
    // ステップ見出し
    children.push(
      new Paragraph({
        heading: HeadingLevel.HEADING_3,
        children: [new TextRun({ 
          text: `手順${stepNum}: ${step.title}`,
          bold: true
        })]
      })
    );

    // 説明文
    if (step.description) {
      children.push(
        new Paragraph({
          style: "BodyText",
          children: [new TextRun({ text: step.description, size: 20, font: FONT_NAME })]
        })
      );
    }

    // 画像（存在する場合）
    if (step.image) {
      const caption = `図${stepNum}: ${step.title}`;
      children.push(...createImageWithCaption(step.image, caption));
    }

    // ポイント・補足（箇条書き）
    if (step.points && step.points.length > 0) {
      children.push(
        new Paragraph({
          spacing: { before: 100 },
          children: [new TextRun({ text: "ポイント:", bold: true, size: 20, font: FONT_NAME })]
        })
      );
      step.points.forEach(point => {
        children.push(
          new Paragraph({
            numbering: { reference: "bullet-list", level: 0 },
            children: [new TextRun({ text: point, size: 20, font: FONT_NAME })]
          })
        );
      });
    }

    // 注意事項（存在する場合）
    if (step.warning) {
      children.push(
        new Paragraph({
          spacing: { before: 100 },
          shading: { fill: COLORS.bg_gray, type: ShadingType.CLEAR },
          children: [
            new TextRun({ text: "⚠️ 注意: ", bold: true, size: 20, font: FONT_NAME }),
            new TextRun({ text: step.warning, size: 20, font: FONT_NAME })
          ]
        })
      );
    }

    // ステップ間のスペース
    children.push(new Paragraph({ children: [] }));
  });

  return children;
}

// ====================
// コマンドライン引数解析
// ====================
function parseArgs() {
  const args = process.argv.slice(2);
  const config = {
    type: 'system',
    title: '業務マニュアル',
    industry: 'general',
    audience: 'beginner',
    version: '1.0',
    author: '',
    department: '',
    output: '/mnt/user-data/outputs/manual.docx',
    images: [],
    content: null,
    stepsJson: null  // 操作手順JSONファイルパス
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--type': config.type = args[++i]; break;
      case '--title': config.title = args[++i]; break;
      case '--industry': config.industry = args[++i]; break;
      case '--audience': config.audience = args[++i]; break;
      case '--version': config.version = args[++i]; break;
      case '--author': config.author = args[++i]; break;
      case '--department': config.department = args[++i]; break;
      case '--output': config.output = args[++i]; break;
      case '--images': config.images = args[++i].split(','); break;
      case '--content': config.content = args[++i]; break;
      case '--steps-json': config.stepsJson = args[++i]; break;
    }
  }
  return config;
}

// ====================
// 共通スタイル定義
// ====================
function getDocumentStyles() {
  return {
    default: {
      document: {
        run: { font: FONT_NAME, size: 20 } // 10pt
      }
    },
    paragraphStyles: [
      {
        id: "Title",
        name: "Title",
        basedOn: "Normal",
        run: { size: 56, bold: true, color: COLORS.black, font: FONT_NAME },
        paragraph: { spacing: { before: 400, after: 200 }, alignment: AlignmentType.CENTER }
      },
      {
        id: "Heading1",
        name: "Heading 1",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 32, bold: true, color: COLORS.black, font: FONT_NAME },
        paragraph: { spacing: { before: 400, after: 200 }, outlineLevel: 0 }
      },
      {
        id: "Heading2",
        name: "Heading 2",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 28, bold: true, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { before: 300, after: 150 }, outlineLevel: 1 }
      },
      {
        id: "Heading3",
        name: "Heading 3",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 24, bold: true, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { before: 200, after: 100 }, outlineLevel: 2 }
      },
      {
        id: "BodyText",
        name: "Body Text",
        basedOn: "Normal",
        run: { size: 20, color: COLORS.dark_gray, font: FONT_NAME },
        paragraph: { spacing: { after: 120, line: 360 } }
      },
      {
        id: "Caption",
        name: "Caption",
        basedOn: "Normal",
        run: { size: 18, italics: true, color: COLORS.medium_gray, font: FONT_NAME },
        paragraph: { alignment: AlignmentType.CENTER, spacing: { before: 60, after: 120 } }
      },
      {
        id: "Note",
        name: "Note",
        basedOn: "Normal",
        run: { size: 18, color: COLORS.medium_gray, font: FONT_NAME },
        paragraph: { spacing: { after: 80 } }
      }
    ]
  };
}

// ====================
// 番号付きリスト設定
// ====================
function getNumberingConfig() {
  return {
    config: [
      {
        reference: "manual-steps",
        levels: [{
          level: 0,
          format: LevelFormat.DECIMAL,
          text: "%1.",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } }
        }]
      },
      {
        reference: "bullet-list",
        levels: [{
          level: 0,
          format: LevelFormat.BULLET,
          text: "•",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } }
        }]
      },
      {
        reference: "checklist",
        levels: [{
          level: 0,
          format: LevelFormat.BULLET,
          text: "□",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } }
        }]
      }
    ]
  };
}

// ====================
// タイトル分割ロジック
// ====================
function splitTitleIntoLines(title) {
  // 分割キーワード（優先度順）
  const splitKeywords = [
    '操作マニュアル',
    '業務マニュアル',
    'マニュアル',
    '手順書',
    '操作手順',
    'ガイドライン',
    'ガイド',
    '規程',
    '規則',
    '要領',
    'フロー',
    '対応マニュアル'
  ];

  for (const keyword of splitKeywords) {
    const index = title.indexOf(keyword);
    if (index > 0) {
      const line1 = title.substring(0, index).trim();
      const line2 = title.substring(index).trim();
      return [line1, line2];
    }
  }

  // キーワードが見つからない場合、長いタイトルは中央付近で分割
  if (title.length > 15) {
    // 助詞や接続詞で分割を試みる
    const breakPoints = ['の', 'に関する', 'における', 'について', '用'];
    for (const bp of breakPoints) {
      const index = title.lastIndexOf(bp);
      if (index > 5 && index < title.length - 5) {
        const line1 = title.substring(0, index + bp.length).trim();
        const line2 = title.substring(index + bp.length).trim();
        if (line2.length > 0) {
          return [line1, line2];
        }
      }
    }
  }

  // 分割不要
  return [title];
}

// ====================
// 表紙生成
// ====================
function generateCoverPage(config) {
  const titleLines = splitTitleIntoLines(config.title);
  
  const children = [
    new Paragraph({ children: [] }), // 上部余白
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] })
  ];

  // タイトル行を追加（意味のある単位で分割）
  titleLines.forEach((line, index) => {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { after: index === titleLines.length - 1 ? 400 : 100 },
        children: [new TextRun({ 
          text: line, 
          bold: true, 
          size: index === 0 ? 72 : 64,  // 2行目はやや小さく
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
      children: [new TextRun({ text: getManualTypeLabel(config.type), size: 28, font: FONT_NAME, color: COLORS.medium_gray })]
    }),
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] })
  );

  // 金融機関向け: 機密区分
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
  children.push(
    new Paragraph({ children: [] }),
    new Paragraph({ children: [] }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text: `バージョン: ${config.version}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
    }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text: `改訂日: ${formatDate(new Date())}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
    })
  );

  if (config.department) {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        children: [new TextRun({ text: `作成部署: ${config.department}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
      })
    );
  }

  if (config.author) {
    children.push(
      new Paragraph({
        alignment: AlignmentType.CENTER,
        children: [new TextRun({ text: `作成者: ${config.author}`, size: 22, font: FONT_NAME, color: COLORS.medium_gray })]
      })
    );
  }

  children.push(new Paragraph({ children: [new PageBreak()] }));
  return children;
}

// ====================
// 目次生成
// ====================
function generateTOC() {
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "目次", bold: true })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "1. はじめに", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      indent: { left: 360 },
      children: [new TextRun({ text: "1.1 本マニュアルの目的", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      indent: { left: 360 },
      children: [new TextRun({ text: "1.2 対象者", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      indent: { left: 360 },
      children: [new TextRun({ text: "1.3 適用範囲", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      indent: { left: 360 },
      children: [new TextRun({ text: "1.4 関連文書", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "2. 操作手順 / 業務フロー / 対応フロー", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "3. エラー対応 / 判断基準 / FAQ集", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "4. 注意事項", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "5. FAQ / トラブルシューティング", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "6. 問い合わせ先", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "改訂履歴", size: 20, font: FONT_NAME })]
    }),
    new Paragraph({ children: [new PageBreak()] })
  ];
}

// ====================
// 「はじめに」セクション生成
// ====================
function generateIntroduction(config) {
  const children = [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "1. はじめに" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "1.1 本マニュアルの目的" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: `本マニュアルは、${config.title}に関する${getManualTypeDescription(config.type)}を提供することを目的としています。` })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "1.2 対象者" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: getAudienceDescription(config.audience) })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "1.3 適用範囲" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[適用範囲を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "1.4 関連文書" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[関連するマニュアル・規程を記載してください]" })]
    })
  ];
  return children;
}

// ====================
// タイプ別メインコンテンツ生成
// ====================
function generateMainContent(config) {
  switch (config.type) {
    case 'system':
      return generateSystemContent(config);
    case 'workflow':
      return generateWorkflowContent(config);
    case 'service':
      return generateServiceContent(config);
    default:
      return generateSystemContent(config);
  }
}

// システム操作マニュアル
function generateSystemContent(config) {
  const children = [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "2. 操作手順" })]
    })
  ];

  // stepsJsonがある場合は画像付き手順を生成
  if (config.stepsJson) {
    const stepsData = loadStepsFromJson(config.stepsJson);
    if (stepsData && stepsData.steps && stepsData.steps.length > 0) {
      console.log(`📷 ${stepsData.steps.length}個の操作手順を画像付きで生成します`);
      children.push(...generateStepsWithImages(stepsData));
    } else {
      // JSONが無効な場合はプレースホルダー
      children.push(...getSystemContentPlaceholder());
    }
  } else {
    // 通常のプレースホルダー
    children.push(...getSystemContentPlaceholder());
  }

  // エラー対応セクション
  children.push(
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "3. エラー対応" })]
    }),
    createErrorTablePlaceholder()
  );

  return children;
}

// システム操作マニュアルのプレースホルダー
function getSystemContentPlaceholder() {
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.1 ログイン / 起動" })]
    }),
    createStepPlaceholder(1, "システムにアクセスします"),
    createStepPlaceholder(2, "ユーザーIDとパスワードを入力します"),
    createStepPlaceholder(3, "「ログイン」ボタンをクリックします"),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.2 基本操作" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[画面説明と操作手順を記載してください]" })]
    }),
    createInputTablePlaceholder(),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.3 データ入力 / 更新" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[データ入力・更新の手順を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.4 出力 / 印刷" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[出力・印刷の手順を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.5 終了 / ログアウト" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[終了・ログアウトの手順を記載してください]" })]
    })
  ];
}

// 業務フローマニュアル
function generateWorkflowContent(config) {
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "2. 業務フロー" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.1 業務概要" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[業務の目的・概要を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.2 フロー図" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[業務フロー図を挿入してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.3 各ステップの詳細" })]
    }),
    createWorkflowStepTable(),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.4 例外処理" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[例外パターンと対応方法を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "3. 判断基準・ルール" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "3.1 承認権限マトリクス" })]
    }),
    createApprovalMatrix()
  ];
}

// 接客・窓口対応マニュアル
function generateServiceContent(config) {
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "2. 対応フロー" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.1 来店時の挨拶・受付" })]
    }),
    createScriptBlock("お客様", "すみません、○○の手続きをしたいのですが..."),
    createScriptBlock("対応者", "いらっしゃいませ。○○の手続きですね。かしこまりました。"),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.2 用件確認" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[用件確認のポイントを記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "2.3 対応パターン別スクリプト" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_3,
      children: [new TextRun({ text: "[パターンA] 基本対応" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[基本対応のスクリプトを記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_3,
      children: [new TextRun({ text: "[パターンB] クレーム対応" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[クレーム対応のスクリプトを記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "3. FAQ集" })]
    }),
    ...createFAQPlaceholder(),
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: "4. エスカレーション基準" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[上席対応が必要なケースを記載してください]" })]
    })
  ];
}

// ====================
// 注意事項セクション
// ====================
function generateCautions(config) {
  const children = [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: config.type === 'service' ? "5. 注意事項" : "4. 注意事項" })]
    })
  ];

  // 金融機関向けセキュリティ注意事項
  if (config.industry === 'finance') {
    children.push(
      ...createNoticeBox("セキュリティに関する注意事項", [
        "本マニュアルは社外持ち出し禁止です",
        "電子データのコピー・転送は禁止です",
        "業務終了後は施錠保管してください",
        "不要になった紙媒体はシュレッダー処理してください"
      ]),
      ...createNoticeBox("コンプライアンス確認事項", [
        "個人情報の取り扱いに注意してください",
        "顧客情報は必要最小限の範囲で閲覧してください",
        "不正アクセス・不正利用は懲戒処分の対象です",
        "疑わしい取引を発見した場合は直ちに報告してください"
      ])
    );
  }

  children.push(
    new Paragraph({
      heading: HeadingLevel.HEADING_2,
      children: [new TextRun({ text: "禁止事項" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "[禁止事項を記載してください]" })]
    })
  );

  return children;
}

// ====================
// FAQ / トラブルシューティング
// ====================
function generateFAQ(config) {
  const sectionNum = config.type === 'service' ? "6" : "5";
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: `${sectionNum}. FAQ / トラブルシューティング` })]
    }),
    ...createFAQPlaceholder()
  ];
}

// ====================
// 問い合わせ先
// ====================
function generateContact(config) {
  const sectionNum = config.type === 'service' ? "7" : "6";
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_1,
      children: [new TextRun({ text: `${sectionNum}. 問い合わせ先` })]
    }),
    createContactTable()
  ];
}

// ====================
// 改訂履歴
// ====================
function generateRevisionHistory(config) {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

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
            createHeaderCell("Ver.", cellBorders),
            createHeaderCell("改訂日", cellBorders),
            createHeaderCell("改訂内容", cellBorders),
            createHeaderCell("改訂者", cellBorders)
          ]
        }),
        new TableRow({
          children: [
            createBodyCell(config.version, cellBorders),
            createBodyCell(formatDate(new Date()), cellBorders),
            createBodyCell("初版作成", cellBorders),
            createBodyCell(config.author || "[作成者]", cellBorders)
          ]
        }),
        new TableRow({
          children: [
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders)
          ]
        }),
        new TableRow({
          children: [
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders),
            createBodyCell("", cellBorders)
          ]
        })
      ]
    })
  ];
}

// ====================
// ヘルパー関数
// ====================
function getManualTypeLabel(type) {
  const labels = {
    system: "システム操作マニュアル",
    workflow: "業務フローマニュアル",
    service: "接客・窓口対応マニュアル"
  };
  return labels[type] || "業務マニュアル";
}

function getManualTypeDescription(type) {
  const descriptions = {
    system: "システムの操作方法と手順",
    workflow: "業務プロセスとフロー",
    service: "接客・窓口対応のガイドライン"
  };
  return descriptions[type] || "業務に関する情報";
}

function getAudienceDescription(audience) {
  const descriptions = {
    beginner: "本マニュアルは、新入社員および業務未経験者を対象としています。基本的な操作から丁寧に解説しています。",
    experienced: "本マニュアルは、業務経験者を対象としています。基本事項は省略し、効率的な操作方法を中心に解説しています。",
    manager: "本マニュアルは、管理者・監督者を対象としています。運用管理や例外対応を中心に解説しています。"
  };
  return descriptions[audience] || descriptions.beginner;
}

function formatDate(date) {
  return `${date.getFullYear()}年${date.getMonth() + 1}月${date.getDate()}日`;
}

function createStepPlaceholder(num, text) {
  return new Paragraph({
    numbering: { reference: "manual-steps", level: 0 },
    children: [new TextRun({ text, size: 20, font: FONT_NAME })]
  });
}

function createHeaderCell(text, borders) {
  return new TableCell({
    borders,
    shading: { fill: COLORS.dark_gray, type: ShadingType.CLEAR },
    children: [new Paragraph({
      alignment: AlignmentType.CENTER,
      children: [new TextRun({ text, bold: true, size: 20, font: FONT_NAME, color: COLORS.white })]
    })]
  });
}

function createBodyCell(text, borders) {
  return new TableCell({
    borders,
    children: [new Paragraph({
      children: [new TextRun({ text, size: 20, font: FONT_NAME })]
    })]
  });
}

function createInputTablePlaceholder() {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [2500, 2500, 4500],
    rows: [
      new TableRow({
        tableHeader: true,
        children: [
          createHeaderCell("項目名", cellBorders),
          createHeaderCell("入力形式", cellBorders),
          createHeaderCell("説明", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("[項目1]", cellBorders),
          createBodyCell("[形式]", cellBorders),
          createBodyCell("[説明]", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("[項目2]", cellBorders),
          createBodyCell("[形式]", cellBorders),
          createBodyCell("[説明]", cellBorders)
        ]
      })
    ]
  });
}

function createErrorTablePlaceholder() {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [3000, 4000, 2500],
    rows: [
      new TableRow({
        tableHeader: true,
        children: [
          createHeaderCell("エラーメッセージ", cellBorders),
          createHeaderCell("原因", cellBorders),
          createHeaderCell("対処方法", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("[エラー1]", cellBorders),
          createBodyCell("[原因]", cellBorders),
          createBodyCell("[対処]", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("[エラー2]", cellBorders),
          createBodyCell("[原因]", cellBorders),
          createBodyCell("[対処]", cellBorders)
        ]
      })
    ]
  });
}

function createWorkflowStepTable() {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [1200, 2500, 3000, 2800],
    rows: [
      new TableRow({
        tableHeader: true,
        children: [
          createHeaderCell("Step", cellBorders),
          createHeaderCell("作業内容", cellBorders),
          createHeaderCell("判断基準", cellBorders),
          createHeaderCell("担当/承認者", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("1", cellBorders),
          createBodyCell("[作業内容]", cellBorders),
          createBodyCell("[判断基準]", cellBorders),
          createBodyCell("[担当者]", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("2", cellBorders),
          createBodyCell("[作業内容]", cellBorders),
          createBodyCell("[判断基準]", cellBorders),
          createBodyCell("[担当者]", cellBorders)
        ]
      })
    ]
  });
}

function createApprovalMatrix() {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [2500, 2500, 2500, 2000],
    rows: [
      new TableRow({
        tableHeader: true,
        children: [
          createHeaderCell("金額/区分", cellBorders),
          createHeaderCell("申請者", cellBorders),
          createHeaderCell("承認者", cellBorders),
          createHeaderCell("決裁者", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("10万円未満", cellBorders),
          createBodyCell("担当者", cellBorders),
          createBodyCell("課長", cellBorders),
          createBodyCell("-", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("10万円以上", cellBorders),
          createBodyCell("担当者", cellBorders),
          createBodyCell("課長", cellBorders),
          createBodyCell("部長", cellBorders)
        ]
      })
    ]
  });
}

function createScriptBlock(speaker, text) {
  const bgColor = speaker === "お客様" ? COLORS.bg_gray : COLORS.white;
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [1500, 8000],
    rows: [
      new TableRow({
        children: [
          new TableCell({
            borders: cellBorders,
            shading: { fill: bgColor, type: ShadingType.CLEAR },
            children: [new Paragraph({
              children: [new TextRun({ text: speaker, bold: true, size: 20, font: FONT_NAME })]
            })]
          }),
          new TableCell({
            borders: cellBorders,
            shading: { fill: bgColor, type: ShadingType.CLEAR },
            children: [new Paragraph({
              children: [new TextRun({ text: `「${text}」`, size: 20, font: FONT_NAME })]
            })]
          })
        ]
      })
    ]
  });
}

function createFAQPlaceholder() {
  return [
    new Paragraph({
      heading: HeadingLevel.HEADING_3,
      children: [new TextRun({ text: "Q1: [よくある質問1]" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "A1: [回答を記載してください]" })]
    }),
    new Paragraph({
      heading: HeadingLevel.HEADING_3,
      children: [new TextRun({ text: "Q2: [よくある質問2]" })]
    }),
    new Paragraph({
      style: "BodyText",
      children: [new TextRun({ text: "A2: [回答を記載してください]" })]
    })
  ];
}

function createContactTable() {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

  return new Table({
    columnWidths: [2500, 3000, 4000],
    rows: [
      new TableRow({
        tableHeader: true,
        children: [
          createHeaderCell("問い合わせ内容", cellBorders),
          createHeaderCell("担当部署", cellBorders),
          createHeaderCell("連絡先", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("システム障害", cellBorders),
          createBodyCell("[IT部門]", cellBorders),
          createBodyCell("[内線番号/メール]", cellBorders)
        ]
      }),
      new TableRow({
        children: [
          createBodyCell("業務内容", cellBorders),
          createBodyCell("[業務部門]", cellBorders),
          createBodyCell("[内線番号/メール]", cellBorders)
        ]
      })
    ]
  });
}

function createNoticeBox(title, items) {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: COLORS.separator };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };
  
  const contentParagraphs = [
    new Paragraph({
      spacing: { after: 100 },
      children: [new TextRun({ text: `【${title}】`, bold: true, size: 22, font: FONT_NAME })]
    })
  ];

  items.forEach(item => {
    contentParagraphs.push(
      new Paragraph({
        numbering: { reference: "checklist", level: 0 },
        children: [new TextRun({ text: item, size: 20, font: FONT_NAME })]
      })
    );
  });

  return [
    new Table({
      columnWidths: [9500],
      rows: [
        new TableRow({
          children: [
            new TableCell({
              borders: cellBorders,
              shading: { fill: COLORS.bg_gray, type: ShadingType.CLEAR },
              children: contentParagraphs
            })
          ]
        })
      ]
    }),
    new Paragraph({ children: [] })
  ];
}

// ====================
// ヘッダー・フッター
// ====================
function getHeader(config) {
  return new Header({
    children: [
      new Paragraph({
        alignment: AlignmentType.RIGHT,
        children: [
          new TextRun({ text: config.title, size: 18, font: FONT_NAME, color: COLORS.light_gray }),
          new TextRun({ text: `  Ver.${config.version}`, size: 18, font: FONT_NAME, color: COLORS.light_gray })
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
async function main() {
  const config = parseArgs();
  console.log("📝 マニュアル生成を開始します...");
  console.log(`   タイプ: ${getManualTypeLabel(config.type)}`);
  console.log(`   タイトル: ${config.title}`);
  console.log(`   業種: ${config.industry}`);
  console.log(`   対象者: ${config.audience}`);

  // ドキュメント構成
  let allChildren = [];
  
  // 表紙
  allChildren = allChildren.concat(generateCoverPage(config));
  
  // 目次
  allChildren = allChildren.concat(generateTOC());
  
  // はじめに
  allChildren = allChildren.concat(generateIntroduction(config));
  
  // メインコンテンツ
  allChildren = allChildren.concat(generateMainContent(config));
  
  // 注意事項
  allChildren = allChildren.concat(generateCautions(config));
  
  // FAQ（serviceタイプは既に含まれている）
  if (config.type !== 'service') {
    allChildren = allChildren.concat(generateFAQ(config));
  }
  
  // 問い合わせ先
  allChildren = allChildren.concat(generateContact(config));
  
  // 改訂履歴
  allChildren = allChildren.concat(generateRevisionHistory(config));

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
      headers: { default: getHeader(config) },
      footers: { default: getFooter() },
      children: allChildren
    }]
  });

  // ファイル出力
  const buffer = await Packer.toBuffer(doc);
  
  // 出力ディレクトリ確保
  const outputDir = path.dirname(config.output);
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
  
  fs.writeFileSync(config.output, buffer);
  console.log(`✅ マニュアルを生成しました: ${config.output}`);
}

main().catch(err => {
  console.error("❌ エラーが発生しました:", err.message);
  process.exit(1);
});
