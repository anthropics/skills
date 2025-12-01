const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell, AlignmentType, 
        WidthType, BorderStyle, ShadingType, HeadingLevel } = require('docx');
const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// Markdownの不要な記号を削除
function cleanMarkdownSymbols(text) {
  // エスケープされたピリオドを通常のピリオドに変換
  text = text.replace(/([0-9]+)\\\./g, '$1.');
  
  // 複数行に分かれた引用ブロックを処理
  const lines = text.split('\n');
  const processedLines = [];
  let i = 0;
  
  while (i < lines.length) {
    const line = lines[i];
    
    // >\(数字\) で始まる行を検出
    if (/^>\s*\\?\([0-9]+\\?\)/.test(line)) {
      // この行から始まる内容を収集（空の>行または次の>\(数字\)が来るまで）
      let combined = line;
      let j = i + 1;
      
      // 次の行が > で始まり、かつ空でなく、かつ >\(数字\) でない限り結合を続ける
      while (j < lines.length && /^>/.test(lines[j]) && !/^>\s*$/.test(lines[j]) && !/^>\s*\\?\([0-9]+\\?\)/.test(lines[j])) {
        combined += ' ' + lines[j].replace(/^>\s*/, '');
        j++;
      }
      
      // 結合した行を処理
      combined = combined.replace(/^>\s*\\?\(([0-9]+)\\?\)\s*/, '($1) ');
      processedLines.push(combined);
      processedLines.push(''); // 項目間に空行を追加して段落を区切る
      i = j;
    } else if (/^>\s*$/.test(line)) {
      // 空の引用行はスキップ（項目の区切り）
      i++;
      continue;
    } else if (/^>/.test(line)) {
      // その他の引用行
      processedLines.push(line.replace(/^>\s*/, ''));
      i++;
    } else {
      // 通常の行
      processedLines.push(line);
      i++;
    }
  }
  
  text = processedLines.join('\n');
  
  // 改行が続く場合、2つにまとめる（段落の区切りを維持）
  text = text.replace(/\n{3,}/g, '\n\n');
  
  // その他のMarkdownエスケープ記号を削除
  text = text.replace(/\\([()[\]{}])/g, '$1');
  
  // Markdown太字記号（**）を除去
  text = text.replace(/\*\*/g, '');
  
  return text;
}

// docxファイルをmarkdownに変換してテキストを抽出
function extractTextFromDocx(docxPath) {
  try {
    const mdPath = docxPath.replace(/\.docx$/, '.md');
    execSync(`pandoc "${docxPath}" -o "${mdPath}"`, { encoding: 'utf-8' });
    let text = fs.readFileSync(mdPath, 'utf-8');
    fs.unlinkSync(mdPath); // 一時ファイル削除
    
    // Markdownの不要な記号を削除
    text = cleanMarkdownSymbols(text);
    
    // 段落番号だけの行を次の行と結合
    const lines = text.split('\n');
    const mergedLines = [];
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      // "数字." だけの行かチェック
      if (/^[0-9]+\.$/.test(line) && i + 1 < lines.length) {
        const nextLine = lines[i + 1].trim();
        if (nextLine !== '') {
          // 次の行と結合
          mergedLines.push(line + ' ' + nextLine);
          i++; // 次の行をスキップ
        } else {
          mergedLines.push(line);
        }
      } else {
        mergedLines.push(lines[i]);
      }
    }
    text = mergedLines.join('\n');
    
    return text;
  } catch (error) {
    console.error(`Error extracting text from ${docxPath}:`, error.message);
    throw error;
  }
}

// Levenshtein距離を計算（編集距離）
function levenshteinDistance(str1, str2) {
  const len1 = str1.length;
  const len2 = str2.length;
  const matrix = Array(len1 + 1).fill(null).map(() => Array(len2 + 1).fill(0));
  
  for (let i = 0; i <= len1; i++) matrix[i][0] = i;
  for (let j = 0; j <= len2; j++) matrix[0][j] = j;
  
  for (let i = 1; i <= len1; i++) {
    for (let j = 1; j <= len2; j++) {
      const cost = str1[i - 1] === str2[j - 1] ? 0 : 1;
      matrix[i][j] = Math.min(
        matrix[i - 1][j] + 1,      // 削除
        matrix[i][j - 1] + 1,      // 挿入
        matrix[i - 1][j - 1] + cost // 置換
      );
    }
  }
  
  return matrix[len1][len2];
}

// 類似度を計算（0.0～1.0、1.0が完全一致）
function calculateSimilarity(str1, str2) {
  if (str1 === str2) return 1.0;
  if (str1.length === 0 && str2.length === 0) return 1.0;
  if (str1.length === 0 || str2.length === 0) return 0.0;
  
  const distance = levenshteinDistance(str1, str2);
  const maxLen = Math.max(str1.length, str2.length);
  return 1.0 - (distance / maxLen);
}

// 段落番号を抽出（例: "2." → 2）
function extractParagraphNumber(text) {
  const match = text.match(/^([0-9]+)\./);
  return match ? parseInt(match[1]) : null;
}

// 段落番号を除去した本文を取得
function getContentWithoutNumber(text) {
  return text.replace(/^[0-9]+\.\s*/, '').trim();
}

// 類似度ベースで段落をマッチング（ハンガリアン法風の貪欲アルゴリズム）
function matchParagraphsBySimilarity(oldParas, newParas, threshold = 0.3) {
  const matches = [];
  const usedOld = new Set();
  const usedNew = new Set();
  
  // 1. 段落番号が一致するものを優先的にマッチング
  for (let i = 0; i < oldParas.length; i++) {
    const oldNum = extractParagraphNumber(oldParas[i]);
    if (oldNum === null) continue;
    
    for (let j = 0; j < newParas.length; j++) {
      const newNum = extractParagraphNumber(newParas[j]);
      if (newNum === oldNum && !usedNew.has(j)) {
        const similarity = calculateSimilarity(
          getContentWithoutNumber(oldParas[i]),
          getContentWithoutNumber(newParas[j])
        );
        
        if (similarity >= threshold) {
          matches.push({ oldIndex: i, newIndex: j, similarity });
          usedOld.add(i);
          usedNew.add(j);
          break;
        }
      }
    }
  }
  
  // 2. 類似度が高いペアを見つけてマッチング（段落番号を除外して比較）
  const candidates = [];
  
  for (let i = 0; i < oldParas.length; i++) {
    if (usedOld.has(i)) continue;
    
    for (let j = 0; j < newParas.length; j++) {
      if (usedNew.has(j)) continue;
      
      // 段落番号を除外して類似度を計算
      const oldContent = getContentWithoutNumber(oldParas[i]);
      const newContent = getContentWithoutNumber(newParas[j]);
      const similarity = calculateSimilarity(oldContent, newContent);
      
      if (similarity >= threshold) {
        candidates.push({ oldIndex: i, newIndex: j, similarity });
      }
    }
  }
  
  // 類似度の高い順にソート
  candidates.sort((a, b) => b.similarity - a.similarity);
  
  // 貪欲法で最適なペアを選択
  for (const candidate of candidates) {
    if (!usedOld.has(candidate.oldIndex) && !usedNew.has(candidate.newIndex)) {
      matches.push(candidate);
      usedOld.add(candidate.oldIndex);
      usedNew.add(candidate.newIndex);
    }
  }
  
  // 3. マッチしなかった段落を記録
  const unmatchedOld = [];
  const unmatchedNew = [];
  
  for (let i = 0; i < oldParas.length; i++) {
    if (!usedOld.has(i)) {
      unmatchedOld.push({ index: i, text: oldParas[i] });
    }
  }
  
  for (let j = 0; j < newParas.length; j++) {
    if (!usedNew.has(j)) {
      unmatchedNew.push({ index: j, text: newParas[j] });
    }
  }
  
  return { matches, unmatchedOld, unmatchedNew };
}

// 意味のある単位（トークン）でのdiff計算
function computeDiff(oldText, newText) {
  const tokenize = (text) => {
    const tokens = [];
    let current = '';
    let lastType = null;
    
    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      let currentType;
      
      if (/[一-龯ぁ-んァ-ヶー]/.test(char)) {
        currentType = 'ja';
      } else if (/[a-zA-Z]/.test(char)) {
        currentType = 'en';
      } else if (/[0-9]/.test(char)) {
        currentType = 'num';
      } else if (/\s/.test(char)) {
        currentType = 'space';
      } else {
        currentType = 'symbol';
      }
      
      if (lastType && lastType !== currentType && currentType !== 'space') {
        if (current) tokens.push(current);
        current = char;
      } else {
        current += char;
      }
      
      lastType = currentType;
    }
    
    if (current) tokens.push(current);
    return tokens;
  };
  
  const oldTokens = tokenize(oldText);
  const newTokens = tokenize(newText);
  
  // LCS（最長共通部分列）を計算
  const lcs = (arr1, arr2) => {
    const m = arr1.length;
    const n = arr2.length;
    const dp = Array(m + 1).fill(null).map(() => Array(n + 1).fill(0));
    
    for (let i = 1; i <= m; i++) {
      for (let j = 1; j <= n; j++) {
        if (arr1[i - 1] === arr2[j - 1]) {
          dp[i][j] = dp[i - 1][j - 1] + 1;
        } else {
          dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
        }
      }
    }
    
    const result = [];
    let i = m, j = n;
    while (i > 0 && j > 0) {
      if (arr1[i - 1] === arr2[j - 1]) {
        result.unshift({ old: i - 1, new: j - 1 });
        i--;
        j--;
      } else if (dp[i - 1][j] > dp[i][j - 1]) {
        i--;
      } else {
        j--;
      }
    }
    
    return result;
  };
  
  const commonTokens = lcs(oldTokens, newTokens);
  const oldChanges = new Set(oldTokens.map((_, i) => i));
  const newChanges = new Set(newTokens.map((_, i) => i));
  
  for (const { old, new: n } of commonTokens) {
    oldChanges.delete(old);
    newChanges.delete(n);
  }
  
  return { oldChanges: Array.from(oldChanges), newChanges: Array.from(newChanges), oldTokens, newTokens };
}

// ハイライト付きのテキストランを作成
function createHighlightedRuns(text, isOld, diffResult) {
  const runs = [];
  const tokens = isOld ? diffResult.oldTokens : diffResult.newTokens;
  const changes = isOld ? new Set(diffResult.oldChanges) : new Set(diffResult.newChanges);
  
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    const isChanged = changes.has(i);
    
    runs.push(new TextRun({
      text: token,
      color: isChanged ? (isOld ? "000000" : "FF0000") : "000000",
      bold: isChanged,
      underline: isChanged ? { type: "single" } : undefined,
      size: 22
    }));
  }
  
  return runs;
}

// 段落を条文単位でグループ化する関数
// 見出しパターンを自動検出
function detectHeadingPattern(paragraphs) {
  // 最初の50行をサンプルとして使用
  const sampleSize = Math.min(50, paragraphs.length);
  const samples = paragraphs.slice(0, sampleSize);
  
  // 各パターンの出現回数をカウント
  const patternScores = {
    legal: 0,           // 第○条
    legalKanji: 0,      // 第○条 (漢数字)
    legalBranch: 0,     // 第○条の○
    numbered: 0,        // 1. (見出し)
    hierarchical: 0,    // 1.1, 1.2.1
    hyphenated: 0,      // 1-1, 1-2
    parentheses: 0,     // (1), （1）
    singleParen: 0,     // 1), 1）
    symbol: 0,          // §, ■, ▪
    bracket: 0,         // 【1】
    english: 0,         // Article, Section
  };
  
  const patterns = {
    legal: /^第[0-9０-９]+条/,
    legalKanji: /^第[一二三四五六七八九十百千]+条/,
    legalBranch: /^第[0-9０-９]+条の[0-9０-９]+/,
    numbered: /^[0-9０-９]+\.\s+[（(]/,
    hierarchical: /^[0-9０-９]+(\.[0-9０-９]+)+\.?\s/,
    hyphenated: /^[0-9０-９]+-[0-9０-９]+\.?\s/,
    parentheses: /^[（(][0-9０-９]+[)）]/,
    singleParen: /^[0-9０-９]+[)）]\s/,
    symbol: /^[§■▪●◆□]/,
    bracket: /^[【［\[][0-9０-９]+[】］\]]/,
    english: /^(Article|Section|Chapter|Part)\s+[0-9]+/i,
  };
  
  for (const para of samples) {
    for (const [name, pattern] of Object.entries(patterns)) {
      if (pattern.test(para)) {
        patternScores[name]++;
      }
    }
  }
  
  // 最もスコアの高いパターンを返す
  let maxScore = 0;
  let detectedPattern = 'numbered'; // デフォルト
  
  for (const [name, score] of Object.entries(patternScores)) {
    if (score > maxScore) {
      maxScore = score;
      detectedPattern = name;
    }
  }
  
  // スコアが0の場合の警告
  if (maxScore === 0) {
    console.log('⚠️  見出しパターンが検出されませんでした。デフォルトパターン(numbered)を使用します。');
  } else {
    console.log(`📊 検出されたパターン: ${detectedPattern} (出現回数: ${maxScore}回)`);
    // 他のパターンのスコアも表示（デバッグ用）
    const otherScores = Object.entries(patternScores)
      .filter(([name, score]) => score > 0 && name !== detectedPattern)
      .map(([name, score]) => `${name}:${score}`)
      .join(', ');
    if (otherScores) {
      console.log(`   その他のパターン: ${otherScores}`);
    }
  }
  
  return detectedPattern;
}

// パターンに基づいて見出しかどうかを判定
function isArticleHeader(para, detectedPattern) {
  // パターンごとの判定ロジック
  const checks = {
    legal: () => /^第[0-9０-９]+条/.test(para),
    legalKanji: () => /^第[一二三四五六七八九十百千]+条/.test(para),
    legalBranch: () => /^第[0-9０-９]+条(の[0-9０-９]+)?/.test(para),
    numbered: () => /^[0-9０-９]+\.\s+[（(]/.test(para),
    hierarchical: () => /^[0-9０-９]+(\.[0-9０-９]+)+\.?\s/.test(para),
    hyphenated: () => /^[0-9０-９]+-[0-9０-９]+\.?\s/.test(para),
    parentheses: () => /^[（(][0-9０-９]+[)）]/.test(para),
    singleParen: () => /^[0-9０-９]+[)）]\s/.test(para),
    symbol: () => /^[§■▪●◆□]/.test(para),
    bracket: () => /^[【［\[][0-9０-９]+[】］\]]/.test(para),
    english: () => /^(Article|Section|Chapter|Part)\s+[0-9]+/i.test(para),
  };
  
  // 検出されたパターンでチェック
  if (checks[detectedPattern] && checks[detectedPattern]()) {
    return true;
  }
  
  // フォールバック: 主要なパターンすべてでチェック
  // (検出精度を上げるため、legal系とnumbered系は常にチェック)
  const fallbackPatterns = ['legal', 'legalKanji', 'legalBranch', 'numbered'];
  for (const pattern of fallbackPatterns) {
    if (checks[pattern] && checks[pattern]()) {
      return true;
    }
  }
  
  return false;
}

function groupByArticle(paragraphs) {
  const articles = [];
  let currentArticle = null;
  
  // 見出しパターンを自動検出
  const detectedPattern = detectHeadingPattern(paragraphs);
  
  for (const para of paragraphs) {
    const isHeader = isArticleHeader(para, detectedPattern);
    
    if (isHeader) {
      if (currentArticle) {
        articles.push(currentArticle);
      }
      currentArticle = {
        header: para,
        paragraphs: []
      };
    } else if (currentArticle) {
      currentArticle.paragraphs.push(para);
    } else {
      // 条文見出しがない場合は、個別の段落として扱う
      articles.push({
        header: '',
        paragraphs: [para]
      });
    }
  }
  
  if (currentArticle) {
    articles.push(currentArticle);
  }
  
  return articles;
}

// 対比表を生成する関数（類似度ベースマッチング版）
function generateComparisonTable(oldParagraphs, newParagraphs, title = "新旧対比表", documentName = "", date = "") {
  const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: "000000" };
  const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };
  
  if (!date) {
    const today = new Date();
    const year = today.getFullYear();
    const month = String(today.getMonth() + 1).padStart(2, '0');
    const day = String(today.getDate()).padStart(2, '0');
    date = `${year}年${month}月${day}日`;
  }
  
  const titleRow = new TableRow({
    children: [
      new TableCell({
        borders: cellBorders,
        width: { size: 4680, type: WidthType.DXA },
        shading: { fill: "F2F2F2", type: ShadingType.CLEAR },
        children: [new Paragraph({
          alignment: AlignmentType.LEFT,
          children: [new TextRun({ text: documentName || "規定名", bold: true, size: 22 })]
        })]
      }),
      new TableCell({
        borders: cellBorders,
        width: { size: 4680, type: WidthType.DXA },
        shading: { fill: "F2F2F2", type: ShadingType.CLEAR },
        children: [new Paragraph({
          alignment: AlignmentType.RIGHT,
          children: [new TextRun({ text: date, bold: true, size: 22 })]
        })]
      })
    ]
  });
  
  const headerRow = new TableRow({
    tableHeader: true,
    children: [
      new TableCell({
        borders: cellBorders,
        width: { size: 4680, type: WidthType.DXA },
        shading: { fill: "D9E1F2", type: ShadingType.CLEAR },
        children: [new Paragraph({
          alignment: AlignmentType.CENTER,
          children: [new TextRun({ text: "変更前", bold: true, size: 24 })]
        })]
      }),
      new TableCell({
        borders: cellBorders,
        width: { size: 4680, type: WidthType.DXA },
        shading: { fill: "FFE699", type: ShadingType.CLEAR },
        children: [new Paragraph({
          alignment: AlignmentType.CENTER,
          children: [new TextRun({ text: "変更後", bold: true, size: 24 })]
        })]
      })
    ]
  });
  
  // 条文単位でグループ化
  const oldArticles = groupByArticle(oldParagraphs);
  const newArticles = groupByArticle(newParagraphs);
  
  const dataRows = [];
  
  // 条文を対応付けて比較（見出しベース）
  const maxArticles = Math.max(oldArticles.length, newArticles.length);
  
  for (let i = 0; i < maxArticles; i++) {
    const oldArticle = oldArticles[i] || { header: '', paragraphs: [] };
    const newArticle = newArticles[i] || { header: '', paragraphs: [] };
    
    // 条文内の段落を類似度ベースでマッチング
    const matchResult = matchParagraphsBySimilarity(
      oldArticle.paragraphs, 
      newArticle.paragraphs,
      0.3 // 類似度閾値30%
    );
    
    // 実質的な変更があるかチェック
    const headerChanged = oldArticle.header !== newArticle.header;
    
    // 実質的に変更がある段落をカウント
    let substantialChanges = 0;
    for (const match of matchResult.matches) {
      const oldPara = oldArticle.paragraphs[match.oldIndex];
      const newPara = newArticle.paragraphs[match.newIndex];
      if (oldPara !== newPara && match.similarity < 0.99) {
        substantialChanges++;
      }
    }
    
    const hasChanges = substantialChanges > 0 || 
                       matchResult.unmatchedOld.length > 0 || 
                       matchResult.unmatchedNew.length > 0 ||
                       headerChanged;
    
    // 変更がない条文はスキップ
    if (!hasChanges) {
      continue;
    }
    
    // 条文見出しと変更のあった段落のみを表示
    const oldCellParagraphs = [];
    const newCellParagraphs = [];
    
    // 条文見出しを追加
    if (oldArticle.header || newArticle.header) {
      oldCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: oldArticle.header, bold: true, size: 24 })]
      }));
      newCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: newArticle.header, bold: true, size: 24 })]
      }));
      
      // 空行を追加
      oldCellParagraphs.push(new Paragraph({ children: [new TextRun({ text: "", size: 22 })] }));
      newCellParagraphs.push(new Paragraph({ children: [new TextRun({ text: "", size: 22 })] }));
    }
    
    // マッチした段落を処理（変更があるものだけ）
    // 類似度が高くても完全一致でない場合のみ表示
    for (const match of matchResult.matches) {
      const oldPara = oldArticle.paragraphs[match.oldIndex];
      const newPara = newArticle.paragraphs[match.newIndex];
      
      // 完全一致または類似度99%以上の場合はスキップ（実質的に同じ内容）
      if (oldPara === newPara || match.similarity >= 0.99) {
        continue;
      }
      
      // 変更あり
      const diffResult = computeDiff(oldPara, newPara);
      oldCellParagraphs.push(new Paragraph({
        children: createHighlightedRuns(oldPara, true, diffResult)
      }));
      newCellParagraphs.push(new Paragraph({
        children: createHighlightedRuns(newPara, false, diffResult)
      }));
    }
    
    // 削除された段落を処理
    for (const { text } of matchResult.unmatchedOld) {
      oldCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: text, color: "FF0000", strike: true, size: 22 })]
      }));
      newCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: "(削除)", italics: true, color: "999999", size: 22 })]
      }));
    }
    
    // 新規追加された段落を処理
    for (const { text } of matchResult.unmatchedNew) {
      oldCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: "(新規追加)", italics: true, color: "999999", size: 22 })]
      }));
      newCellParagraphs.push(new Paragraph({
        children: [new TextRun({ text: text, color: "0000FF", bold: true, size: 22 })]
      }));
    }
    
    // 条文見出し以外に内容がない場合（空欄）はスキップ
    // 見出し + 空行のみ = 2段落
    if (oldCellParagraphs.length <= 2 && newCellParagraphs.length <= 2) {
      continue;
    }
    
    dataRows.push(new TableRow({
      children: [
        new TableCell({
          borders: cellBorders,
          width: { size: 4680, type: WidthType.DXA },
          verticalAlign: "top",
          children: oldCellParagraphs
        }),
        new TableCell({
          borders: cellBorders,
          width: { size: 4680, type: WidthType.DXA },
          verticalAlign: "top",
          children: newCellParagraphs
        })
      ]
    }));
  }
  
  const doc = new Document({
    styles: {
      default: { document: { run: { font: "Yu Gothic", size: 22 } } },
      paragraphStyles: [
        { id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal",
          run: { size: 32, bold: true, color: "000000", font: "Yu Gothic" },
          paragraph: { spacing: { before: 240, after: 240 }, alignment: AlignmentType.CENTER } }
      ]
    },
    sections: [{
      properties: {
        page: { margin: { top: 720, right: 720, bottom: 720, left: 720 } }
      },
      children: [
        new Paragraph({
          heading: HeadingLevel.HEADING_1,
          children: [new TextRun(title)]
        }),
        new Paragraph({ children: [new TextRun("")] }),
        new Table({
          alignment: AlignmentType.CENTER,
          columnWidths: [4680, 4680],
          margins: { top: 100, bottom: 100, left: 100, right: 100 },
          rows: [titleRow, headerRow, ...dataRows]
        })
      ]
    }]
  });
  
  return doc;
}

// コマンドライン引数から入力を取得
if (process.argv.length < 4) {
  console.log("使用方法: node comparison_docx_generator_v3.js <変更前.docx> <変更後.docx> [出力ファイル名] [規定名] [日付]");
  console.log("例: node comparison_docx_generator_v3.js old.docx new.docx output.docx \"就業規則\" \"2025年10月30日\"");
  process.exit(1);
}

const oldFile = process.argv[2];
const newFile = process.argv[3];
const outputFile = process.argv[4] || "comparison_table.docx";
const documentName = process.argv[5] || "";
const date = process.argv[6] || "";

console.log("📄 変更前ファイルを読み込み中...");
const oldText = extractTextFromDocx(oldFile);
console.log("📄 変更後ファイルを読み込み中...");
const newText = extractTextFromDocx(newFile);

const oldParagraphs = oldText.split('\n').filter(p => p.trim() !== '');
const newParagraphs = newText.split('\n').filter(p => p.trim() !== '');

console.log("🔍 変更箇所を検出中（類似度ベースマッチング）...");
const doc = generateComparisonTable(oldParagraphs, newParagraphs, "新旧対比表", documentName, date);

console.log("📝 新旧対比表を生成中...");
Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync(outputFile, buffer);
  console.log(`\n✅ 新旧対比表を生成しました: ${outputFile}`);
  if (documentName) console.log(`📋 規定名: ${documentName}`);
  if (date) console.log(`📅 日付: ${date}`);
  console.log(`📊 変更前: ${oldParagraphs.length}段落`);
  console.log(`📊 変更後: ${newParagraphs.length}段落`);
  
  // 条文単位で変更をカウント
  const oldArticles = groupByArticle(oldParagraphs);
  const newArticles = groupByArticle(newParagraphs);
  
  let changedArticleCount = 0;
  let changedParagraphCount = 0;
  let addedParagraphCount = 0;
  let deletedParagraphCount = 0;
  const maxArticles = Math.max(oldArticles.length, newArticles.length);
  
  for (let i = 0; i < maxArticles; i++) {
    const oldArticle = oldArticles[i] || { header: '', paragraphs: [] };
    const newArticle = newArticles[i] || { header: '', paragraphs: [] };
    
    const matchResult = matchParagraphsBySimilarity(
      oldArticle.paragraphs, 
      newArticle.paragraphs,
      0.3
    );
    
    const headerChanged = oldArticle.header !== newArticle.header;
    let articleHasChanges = headerChanged;
    
    // 変更された段落をカウント（類似度99%以上は除外）
    for (const match of matchResult.matches) {
      const oldPara = oldArticle.paragraphs[match.oldIndex];
      const newPara = newArticle.paragraphs[match.newIndex];
      
      if (oldPara !== newPara && match.similarity < 0.99) {
        articleHasChanges = true;
        changedParagraphCount++;
      }
    }
    
    // 削除・追加をカウント
    deletedParagraphCount += matchResult.unmatchedOld.length;
    addedParagraphCount += matchResult.unmatchedNew.length;
    
    if (matchResult.unmatchedOld.length > 0 || matchResult.unmatchedNew.length > 0) {
      articleHasChanges = true;
    }
    
    if (articleHasChanges) {
      changedArticleCount++;
    }
  }
  
  console.log(`🔄 変更された条文: ${changedArticleCount}個`);
  console.log(`📝 変更された段落: ${changedParagraphCount}個`);
  console.log(`➕ 新規追加段落: ${addedParagraphCount}個`);
  console.log(`➖ 削除された段落: ${deletedParagraphCount}個`);
});
