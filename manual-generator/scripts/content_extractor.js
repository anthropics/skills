/**
 * Content Extractor - 既存マニュアルからコンテンツを抽出
 * PDF/Word → 構造化JSON
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// ====================
// メイン抽出関数
// ====================

/**
 * ファイルからコンテンツを抽出
 * @param {string} filePath - 入力ファイルパス（PDF/DOCX）
 * @param {string} outputPath - 出力JSONパス
 */
async function extractContent(filePath, outputPath) {
  const ext = path.extname(filePath).toLowerCase();
  
  console.log(`📄 ファイル読み込み: ${filePath}`);
  console.log(`   形式: ${ext}`);

  let rawText = '';
  
  // ファイル形式に応じて抽出
  if (ext === '.docx') {
    rawText = extractFromDocx(filePath);
  } else if (ext === '.pdf') {
    rawText = extractFromPdf(filePath);
  } else {
    throw new Error(`未対応の形式です: ${ext}`);
  }

  // 構造解析
  console.log('🔍 構造解析中...');
  const structure = analyzeStructure(rawText);
  
  // JSON出力
  const output = {
    source: path.basename(filePath),
    extractedAt: new Date().toISOString(),
    structure: structure
  };

  fs.writeFileSync(outputPath, JSON.stringify(output, null, 2), 'utf-8');
  console.log(`✅ 構造抽出完了: ${outputPath}`);
  console.log(`   セクション数: ${structure.sections.length}`);
  
  return output;
}

// ====================
// Word抽出
// ====================
function extractFromDocx(filePath) {
  const tempMd = '/tmp/extracted_manual.md';
  
  try {
    // pandocでMarkdown変換
    execSync(`pandoc "${filePath}" -o "${tempMd}" --wrap=none`, { encoding: 'utf-8' });
    const content = fs.readFileSync(tempMd, 'utf-8');
    fs.unlinkSync(tempMd);
    return content;
  } catch (e) {
    console.error('❌ Word抽出エラー:', e.message);
    throw e;
  }
}

// ====================
// PDF抽出
// ====================
function extractFromPdf(filePath) {
  const tempTxt = '/tmp/extracted_manual.txt';
  
  try {
    // pdftotextでテキスト抽出
    execSync(`pdftotext -layout "${filePath}" "${tempTxt}"`, { encoding: 'utf-8' });
    const content = fs.readFileSync(tempTxt, 'utf-8');
    fs.unlinkSync(tempTxt);
    return content;
  } catch (e) {
    console.error('❌ PDF抽出エラー:', e.message);
    throw e;
  }
}

// ====================
// 構造解析
// ====================
function analyzeStructure(rawText) {
  const lines = rawText.split('\n');
  const structure = {
    title: '',
    sections: [],
    metadata: {}
  };

  let currentSection = null;
  let currentSubsection = null;
  let contentBuffer = [];

  // 見出しパターン
  const patterns = {
    // Markdownスタイル
    mdH1: /^#\s+(.+)$/,
    mdH2: /^##\s+(.+)$/,
    mdH3: /^###\s+(.+)$/,
    // 数字スタイル
    numH1: /^(\d+)\.\s+(.+)$/,
    numH2: /^(\d+)\.(\d+)\s+(.+)$/,
    numH3: /^(\d+)\.(\d+)\.(\d+)\s+(.+)$/,
    // 日本語スタイル
    jpH1: /^第(\d+)章\s*[:：]?\s*(.*)$/,
    jpH2: /^第(\d+)条\s*[:：]?\s*(.*)$/,
    jpSection: /^[【\[](.*)[】\]]$/,
    // 括弧スタイル
    parenNum: /^\((\d+)\)\s+(.+)$/,
    // 箇条書き
    bullet: /^[\-\*•・]\s+(.+)$/,
    // 番号リスト
    numList: /^(\d+)[\.）\)]\s+(.+)$/
  };

  // メタデータ抽出パターン
  const metaPatterns = {
    version: /(?:バージョン|Ver\.?|version)\s*[:：]?\s*([0-9.]+)/i,
    date: /(?:作成日|改訂日|日付|Date)\s*[:：]?\s*(\d{4}[年\/\-]\d{1,2}[月\/\-]\d{1,2}日?)/i,
    author: /(?:作成者|Author)\s*[:：]?\s*(.+)/i,
    department: /(?:部署|作成部門)\s*[:：]?\s*(.+)/i
  };

  // 最初の見出しをタイトルとして抽出
  let titleFound = false;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    
    if (!line) {
      if (contentBuffer.length > 0) {
        contentBuffer.push('');
      }
      continue;
    }

    // メタデータ抽出
    for (const [key, pattern] of Object.entries(metaPatterns)) {
      const match = line.match(pattern);
      if (match) {
        structure.metadata[key] = match[1].trim();
      }
    }

    // 見出し判定
    let headingLevel = 0;
    let headingText = '';

    // Markdown H1
    let match = line.match(patterns.mdH1);
    if (match) {
      headingLevel = 1;
      headingText = match[1];
    }
    
    // Markdown H2
    if (!headingLevel) {
      match = line.match(patterns.mdH2);
      if (match) {
        headingLevel = 2;
        headingText = match[1];
      }
    }

    // Markdown H3
    if (!headingLevel) {
      match = line.match(patterns.mdH3);
      if (match) {
        headingLevel = 3;
        headingText = match[1];
      }
    }

    // 数字スタイル H1 (1. xxx)
    if (!headingLevel) {
      match = line.match(patterns.numH1);
      if (match && !line.match(patterns.numH2)) {
        headingLevel = 1;
        headingText = match[2];
      }
    }

    // 数字スタイル H2 (1.1 xxx)
    if (!headingLevel) {
      match = line.match(patterns.numH2);
      if (match && !line.match(patterns.numH3)) {
        headingLevel = 2;
        headingText = match[3];
      }
    }

    // 数字スタイル H3 (1.1.1 xxx)
    if (!headingLevel) {
      match = line.match(patterns.numH3);
      if (match) {
        headingLevel = 3;
        headingText = match[4];
      }
    }

    // 日本語 第X章
    if (!headingLevel) {
      match = line.match(patterns.jpH1);
      if (match) {
        headingLevel = 1;
        headingText = match[2] || `第${match[1]}章`;
      }
    }

    // 【セクション】スタイル
    if (!headingLevel) {
      match = line.match(patterns.jpSection);
      if (match) {
        headingLevel = 2;
        headingText = match[1];
      }
    }

    // 見出しが見つかった場合
    if (headingLevel > 0) {
      // 最初の見出しをタイトルに
      if (!titleFound && headingLevel === 1) {
        structure.title = headingText;
        titleFound = true;
        continue;
      }

      // 前のセクションのコンテンツを保存
      if (currentSubsection) {
        currentSubsection.content = contentBuffer.join('\n').trim();
        contentBuffer = [];
      } else if (currentSection) {
        currentSection.content = contentBuffer.join('\n').trim();
        contentBuffer = [];
      }

      // 新しいセクション/サブセクション作成
      if (headingLevel === 1 || headingLevel === 2) {
        if (currentSection) {
          structure.sections.push(currentSection);
        }
        currentSection = {
          level: headingLevel,
          title: headingText,
          content: '',
          subsections: []
        };
        currentSubsection = null;
      } else if (headingLevel === 3 && currentSection) {
        if (currentSubsection) {
          currentSection.subsections.push(currentSubsection);
        }
        currentSubsection = {
          level: headingLevel,
          title: headingText,
          content: ''
        };
      }
    } else {
      // 通常のコンテンツ
      contentBuffer.push(line);
    }
  }

  // 最後のセクションを保存
  if (currentSubsection) {
    currentSubsection.content = contentBuffer.join('\n').trim();
    if (currentSection) {
      currentSection.subsections.push(currentSubsection);
    }
  } else if (currentSection) {
    currentSection.content = contentBuffer.join('\n').trim();
  }
  
  if (currentSection) {
    structure.sections.push(currentSection);
  }

  return structure;
}

// ====================
// CLI実行
// ====================
if (require.main === module) {
  const args = process.argv.slice(2);
  
  if (args.length < 2) {
    console.log('使用方法: node content_extractor.js <入力ファイル> <出力JSON>');
    console.log('例: node content_extractor.js manual.docx extracted.json');
    process.exit(1);
  }

  const inputFile = args[0];
  const outputFile = args[1];

  if (!fs.existsSync(inputFile)) {
    console.error(`❌ ファイルが見つかりません: ${inputFile}`);
    process.exit(1);
  }

  extractContent(inputFile, outputFile)
    .then(() => console.log('完了'))
    .catch(err => {
      console.error('エラー:', err.message);
      process.exit(1);
    });
}

module.exports = { extractContent, analyzeStructure };
