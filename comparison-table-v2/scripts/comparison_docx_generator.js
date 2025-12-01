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
    
    return text;
  } catch (error) {
    console.error(`Error extracting text from ${docxPath}:`, error.message);
    throw error;
  }
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
        currentType = 'other';
      }
      
      if (lastType === currentType && currentType !== 'other') {
        current += char;
      } else {
        if (current) tokens.push(current);
        current = char;
        lastType = currentType;
      }
    }
    if (current) tokens.push(current);
    
    return tokens;
  };
  
  const oldTokens = tokenize(oldText);
  const newTokens = tokenize(newText);
  
  const dp = Array(oldTokens.length + 1).fill(null).map(() => 
    Array(newTokens.length + 1).fill(0)
  );
  
  for (let i = 1; i <= oldTokens.length; i++) {
    for (let j = 1; j <= newTokens.length; j++) {
      if (oldTokens[i-1] === newTokens[j-1]) {
        dp[i][j] = dp[i-1][j-1] + 1;
      } else {
        dp[i][j] = Math.max(dp[i-1][j], dp[i][j-1]);
      }
    }
  }
  
  const lcs = [];
  let i = oldTokens.length, j = newTokens.length;
  while (i > 0 && j > 0) {
    if (oldTokens[i-1] === newTokens[j-1]) {
      lcs.unshift([i-1, j-1]);
      i--; j--;
    } else if (dp[i-1][j] > dp[i][j-1]) {
      i--;
    } else {
      j--;
    }
  }
  
  return { lcs, oldTokens, newTokens };
}

// 変更箇所を色付けしたTextRunを生成
function createHighlightedRuns(text, isOld, diffResult) {
  const { lcs, oldTokens, newTokens } = diffResult;
  const tokens = isOld ? oldTokens : newTokens;
  const runs = [];
  const lcsSet = new Set(lcs.map(pair => isOld ? pair[0] : pair[1]));
  
  let currentText = '';
  let currentIsChanged = null;
  
  for (let i = 0; i < tokens.length; i++) {
    const isChanged = !lcsSet.has(i);
    
    if (currentIsChanged !== null && currentIsChanged !== isChanged) {
      runs.push(new TextRun({
        text: currentText,
        color: currentIsChanged ? (isOld ? "000000" : "FF0000") : "000000",
        bold: currentIsChanged,
        underline: currentIsChanged ? { type: "single" } : undefined,
        size: 22
      }));
      currentText = '';
    }
    
    currentText += tokens[i];
    currentIsChanged = isChanged;
  }
  
  if (currentText) {
    runs.push(new TextRun({
      text: currentText,
      color: currentIsChanged ? (isOld ? "000000" : "FF0000") : "000000",
      bold: currentIsChanged,
      underline: currentIsChanged ? { type: "single" } : undefined,
      size: 22
    }));
  }
  
  return runs;
}

// 段落を条文単位でグループ化する関数
function groupByArticle(paragraphs) {
  const articles = [];
  let currentArticle = null;
  
  for (const para of paragraphs) {
    // 「第○条」で始まる行を条文見出しとして検出
    if (/^第[0-9０-９]+条/.test(para)) {
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

// 対比表を生成する関数（条文単位で変更された段落のみ）
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
  
  // 条文を対応付けて比較
  const maxArticles = Math.max(oldArticles.length, newArticles.length);
  
  for (let i = 0; i < maxArticles; i++) {
    const oldArticle = oldArticles[i] || { header: '', paragraphs: [] };
    const newArticle = newArticles[i] || { header: '', paragraphs: [] };
    
    // 条文内の段落を比較して変更を検出
    const maxParas = Math.max(oldArticle.paragraphs.length, newArticle.paragraphs.length);
    const changedParagraphs = [];
    
    for (let j = 0; j < maxParas; j++) {
      const oldPara = oldArticle.paragraphs[j] || "";
      const newPara = newArticle.paragraphs[j] || "";
      
      if (oldPara !== newPara) {
        changedParagraphs.push({ oldPara, newPara });
      }
    }
    
    // 条文見出しの変更も検出
    const headerChanged = oldArticle.header !== newArticle.header;
    
    // 変更がない条文はスキップ
    if (changedParagraphs.length === 0 && !headerChanged) {
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
    
    // 変更のあった段落のみを追加
    for (const { oldPara, newPara } of changedParagraphs) {
      if (oldPara === "" && newPara !== "") {
        // 新規追加
        oldCellParagraphs.push(new Paragraph({
          children: [new TextRun({ text: "(新規追加)", italics: true, color: "999999", size: 22 })]
        }));
        newCellParagraphs.push(new Paragraph({
          children: [new TextRun({ text: newPara, color: "0000FF", bold: true, size: 22 })]
        }));
      } else if (oldPara !== "" && newPara === "") {
        // 削除
        oldCellParagraphs.push(new Paragraph({
          children: [new TextRun({ text: oldPara, color: "FF0000", strike: true, size: 22 })]
        }));
        newCellParagraphs.push(new Paragraph({
          children: [new TextRun({ text: "(削除)", italics: true, color: "999999", size: 22 })]
        }));
      } else {
        // 変更あり
        const diffResult = computeDiff(oldPara, newPara);
        oldCellParagraphs.push(new Paragraph({
          children: createHighlightedRuns(oldPara, true, diffResult)
        }));
        newCellParagraphs.push(new Paragraph({
          children: createHighlightedRuns(newPara, false, diffResult)
        }));
      }
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
  console.log("使用方法: node comparison_docx_generator.js <変更前.docx> <変更後.docx> [出力ファイル名] [規定名] [日付]");
  console.log("例: node comparison_docx_generator.js old.docx new.docx output.docx \"就業規則\" \"2025年10月30日\"");
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

console.log("🔍 変更箇所を検出中...");
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
  const maxArticles = Math.max(oldArticles.length, newArticles.length);
  
  for (let i = 0; i < maxArticles; i++) {
    const oldArticle = oldArticles[i] || { header: '', paragraphs: [] };
    const newArticle = newArticles[i] || { header: '', paragraphs: [] };
    
    const maxParas = Math.max(oldArticle.paragraphs.length, newArticle.paragraphs.length);
    let articleHasChanges = oldArticle.header !== newArticle.header;
    
    for (let j = 0; j < maxParas; j++) {
      const oldPara = oldArticle.paragraphs[j] || "";
      const newPara = newArticle.paragraphs[j] || "";
      
      if (oldPara !== newPara) {
        articleHasChanges = true;
        changedParagraphCount++;
      }
    }
    
    if (articleHasChanges) {
      changedArticleCount++;
    }
  }
  
  console.log(`🔄 変更された条文: ${changedArticleCount}個`);
  console.log(`🔄 変更された段落: ${changedParagraphCount}個`);
});
