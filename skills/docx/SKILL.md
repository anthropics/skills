---
name: docx
description: "当用户需要创建、读取、编辑或处理 Word 文档（.docx 文件）时，使用此技能。触发条件包括：提及"Word 文档"、".docx"，或要求生成带有目录、标题、页码、信头等格式的专业文档。也适用于从 .docx 文件中提取或重组内容、在文档中插入或替换图片、在 Word 文件中执行查找替换、处理修订和批注，或将内容转换为精美的 Word 文档。如果用户要求以 Word 或 .docx 文件格式输出"报告"、"备忘录"、"信函"、"模板"或类似文档，请使用此技能。不适用于 PDF、电子表格、Google Docs 或与文档生成无关的编程任务。"
license: Proprietary. LICENSE.txt has complete terms
---

# DOCX 创建、编辑与分析

## 概述

.docx 文件是一个包含 XML 文件的 ZIP 压缩包。

## 快速参考

| 任务 | 方法 |
|------|------|
| 读取/分析内容 | `pandoc` 或解压查看原始 XML |
| 创建新文档 | 使用 `docx-js` — 参见下方"创建新文档" |
| 编辑现有文档 | 解压 → 编辑 XML → 重新打包 — 参见下方"编辑现有文档" |

### 将 .doc 转换为 .docx

旧版 `.doc` 文件必须先转换才能编辑：

```bash
python scripts/office/soffice.py --headless --convert-to docx document.doc
```

### 读取内容

```bash
# 提取带修订的文本
pandoc --track-changes=all document.docx -o output.md

# 访问原始 XML
python scripts/office/unpack.py document.docx unpacked/
```

### 转换为图片

```bash
python scripts/office/soffice.py --headless --convert-to pdf document.docx
pdftoppm -jpeg -r 150 document.pdf page
```

### 接受修订

生成一份已接受所有修订的干净文档（需要 LibreOffice）：

```bash
python scripts/accept_changes.py input.docx output.docx
```

---

## 创建新文档

使用 JavaScript 生成 .docx 文件，然后验证。安装：`npm install -g docx`

### 设置
```javascript
const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell, ImageRun,
        Header, Footer, AlignmentType, PageOrientation, LevelFormat, ExternalHyperlink,
        TableOfContents, HeadingLevel, BorderStyle, WidthType, ShadingType,
        VerticalAlign, PageNumber, PageBreak } = require('docx');

const doc = new Document({ sections: [{ children: [/* 内容 */] }] });
Packer.toBuffer(doc).then(buffer => fs.writeFileSync("doc.docx", buffer));
```

### 验证
创建文件后进行验证。如果验证失败，解压、修复 XML 后重新打包。
```bash
python scripts/office/validate.py doc.docx
```

### 页面尺寸

```javascript
// 关键：docx-js 默认为 A4 纸张，而非美式 Letter
// 务必显式设置页面尺寸以确保一致性
sections: [{
  properties: {
    page: {
      size: {
        width: 12240,   // 8.5 英寸（DXA 单位）
        height: 15840   // 11 英寸（DXA 单位）
      },
      margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 } // 1 英寸页边距
    }
  },
  children: [/* 内容 */]
}]
```

**常用页面尺寸（DXA 单位，1440 DXA = 1 英寸）：**

| 纸张 | 宽度 | 高度 | 内容宽度（1 英寸页边距） |
|------|------|------|--------------------------|
| 美式 Letter | 12,240 | 15,840 | 9,360 |
| A4（默认） | 11,906 | 16,838 | 9,026 |

**横向方向：** docx-js 会在内部交换宽高值，因此传入纵向尺寸，让它自行处理交换：
```javascript
size: {
  width: 12240,   // 传入短边作为宽度
  height: 15840,  // 传入长边作为高度
  orientation: PageOrientation.LANDSCAPE  // docx-js 会在 XML 中交换它们
},
// 内容宽度 = 15840 - 左页边距 - 右页边距（使用长边）
```

### 样式（覆盖内置标题）

使用 Arial 作为默认字体（通用支持）。保持标题为黑色以确保可读性。

```javascript
const doc = new Document({
  styles: {
    default: { document: { run: { font: "Arial", size: 24 } } }, // 默认 12pt
    paragraphStyles: [
      // 重要：使用精确的 ID 来覆盖内置样式
      { id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 32, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 240, after: 240 }, outlineLevel: 0 } }, // 目录需要 outlineLevel
      { id: "Heading2", name: "Heading 2", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 28, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 180, after: 180 }, outlineLevel: 1 } },
    ]
  },
  sections: [{
    children: [
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Title")] }),
    ]
  }]
});
```

### 列表（切勿使用 Unicode 项目符号）

```javascript
// ❌ 错误 - 永远不要手动插入项目符号字符
new Paragraph({ children: [new TextRun("• Item")] })  // 错误
new Paragraph({ children: [new TextRun("\u2022 Item")] })  // 错误

// ✅ 正确 - 使用 numbering 配置和 LevelFormat.BULLET
const doc = new Document({
  numbering: {
    config: [
      { reference: "bullets",
        levels: [{ level: 0, format: LevelFormat.BULLET, text: "•", alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
      { reference: "numbers",
        levels: [{ level: 0, format: LevelFormat.DECIMAL, text: "%1.", alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
    ]
  },
  sections: [{
    children: [
      new Paragraph({ numbering: { reference: "bullets", level: 0 },
        children: [new TextRun("Bullet item")] }),
      new Paragraph({ numbering: { reference: "numbers", level: 0 },
        children: [new TextRun("Numbered item")] }),
    ]
  }]
});

// ⚠️ 每个 reference 创建独立的编号序列
// 相同 reference = 继续编号（1,2,3 然后 4,5,6）
// 不同 reference = 重新编号（1,2,3 然后 1,2,3）
```

### 表格

**关键：表格需要双重宽度设置** — 同时在表格上设置 `columnWidths` 和在每个单元格上设置 `width`。缺少任一设置，表格在某些平台上会渲染异常。

```javascript
// 关键：始终设置表格宽度以确保一致渲染
// 关键：使用 ShadingType.CLEAR（而非 SOLID）以避免黑色背景
const border = { style: BorderStyle.SINGLE, size: 1, color: "CCCCCC" };
const borders = { top: border, bottom: border, left: border, right: border };

new Table({
  width: { size: 9360, type: WidthType.DXA }, // 始终使用 DXA（百分比在 Google Docs 中会出问题）
  columnWidths: [4680, 4680], // 总和必须等于表格宽度（DXA：1440 = 1 英寸）
  rows: [
    new TableRow({
      children: [
        new TableCell({
          borders,
          width: { size: 4680, type: WidthType.DXA }, // 每个单元格也要设置
          shading: { fill: "D5E8F0", type: ShadingType.CLEAR }, // 用 CLEAR 而非 SOLID
          margins: { top: 80, bottom: 80, left: 120, right: 120 }, // 单元格内边距（内部的，不会增加宽度）
          children: [new Paragraph({ children: [new TextRun("Cell")] })]
        })
      ]
    })
  ]
})
```

**表格宽度计算：**

始终使用 `WidthType.DXA` — `WidthType.PERCENTAGE` 在 Google Docs 中会出问题。

```javascript
// 表格宽度 = columnWidths 之和 = 内容宽度
// 美式 Letter 1 英寸页边距：12240 - 2880 = 9360 DXA
width: { size: 9360, type: WidthType.DXA },
columnWidths: [7000, 2360]  // 总和必须等于表格宽度
```

**宽度规则：**
- **始终使用 `WidthType.DXA`** — 绝不使用 `WidthType.PERCENTAGE`（与 Google Docs 不兼容）
- 表格宽度必须等于 `columnWidths` 之和
- 单元格 `width` 必须与对应的 `columnWidth` 一致
- 单元格 `margins` 是内边距 — 减少内容区域，不会增加单元格宽度
- 全宽表格：使用内容宽度（页面宽度减去左右页边距）

### 图片

```javascript
// 关键：type 参数是必需的
new Paragraph({
  children: [new ImageRun({
    type: "png", // 必填：png, jpg, jpeg, gif, bmp, svg
    data: fs.readFileSync("image.png"),
    transformation: { width: 200, height: 150 },
    altText: { title: "Title", description: "Desc", name: "Name" } // 三个都是必填的
  })]
})
```

### 分页符

```javascript
// 关键：PageBreak 必须放在 Paragraph 内部
new Paragraph({ children: [new PageBreak()] })

// 或使用 pageBreakBefore
new Paragraph({ pageBreakBefore: true, children: [new TextRun("New page")] })
```

### 目录

```javascript
// 关键：标题必须只使用 HeadingLevel — 不能用自定义样式
new TableOfContents("Table of Contents", { hyperlink: true, headingStyleRange: "1-3" })
```

### 页眉/页脚

```javascript
sections: [{
  properties: {
    page: { margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 } } // 1440 = 1 英寸
  },
  headers: {
    default: new Header({ children: [new Paragraph({ children: [new TextRun("Header")] })] })
  },
  footers: {
    default: new Footer({ children: [new Paragraph({
      children: [new TextRun("Page "), new TextRun({ children: [PageNumber.CURRENT] })]
    })] })
  },
  children: [/* 内容 */]
}]
```

### docx-js 关键规则

- **显式设置页面尺寸** — docx-js 默认为 A4；美国文档使用美式 Letter（12240 x 15840 DXA）
- **横向：传入纵向尺寸** — docx-js 会在内部交换宽高；将短边作为 `width`，长边作为 `height`，并设置 `orientation: PageOrientation.LANDSCAPE`
- **切勿使用 `\n`** — 使用独立的 Paragraph 元素
- **切勿使用 Unicode 项目符号** — 使用 `LevelFormat.BULLET` 配合 numbering 配置
- **PageBreak 必须在 Paragraph 内** — 独立使用会生成无效 XML
- **ImageRun 需要 `type`** — 始终指定 png/jpg 等
- **始终使用 DXA 设置表格 `width`** — 绝不使用 `WidthType.PERCENTAGE`（在 Google Docs 中不兼容）
- **表格需要双重宽度** — `columnWidths` 数组和单元格 `width` 都必须设置且匹配
- **表格宽度 = columnWidths 之和** — 使用 DXA 时确保精确相加
- **始终添加单元格内边距** — 使用 `margins: { top: 80, bottom: 80, left: 120, right: 120 }` 以获得合适的间距
- **使用 `ShadingType.CLEAR`** — 绝不用 SOLID 来设置表格底纹
- **目录需要仅使用 HeadingLevel** — 标题段落不能使用自定义样式
- **覆盖内置样式** — 使用精确的 ID："Heading1"、"Heading2" 等
- **包含 `outlineLevel`** — 目录需要此属性（H1 为 0，H2 为 1，依此类推）

---

## 编辑现有文档

**严格按照以下 3 个步骤顺序操作。**

### 步骤 1：解压
```bash
python scripts/office/unpack.py document.docx unpacked/
```
提取 XML、美化打印、合并相邻 run、并将智能引号转换为 XML 实体（`&#x201C;` 等）以确保编辑后不丢失。使用 `--merge-runs false` 可跳过 run 合并。

### 步骤 2：编辑 XML

编辑 `unpacked/word/` 中的文件。请参考下方的 XML 参考获取编辑模式。

**修订和批注的作者使用 "Claude"**，除非用户明确要求使用其他名称。

**直接使用 Edit 工具进行字符串替换，不要编写 Python 脚本。** 脚本会引入不必要的复杂性。Edit 工具能清楚地展示正在替换的内容。

**关键：新内容使用智能引号。** 添加包含撇号或引号的文本时，使用 XML 实体生成智能引号：
```xml
<!-- 使用这些实体来实现专业排版效果 -->
<w:t>Here&#x2019;s a quote: &#x201C;Hello&#x201D;</w:t>
```
| 实体 | 字符 |
|------|------|
| `&#x2018;` | '（左单引号） |
| `&#x2019;` | '（右单引号/撇号） |
| `&#x201C;` | "（左双引号） |
| `&#x201D;` | "（右双引号） |

**添加批注：** 使用 `comment.py` 处理跨多个 XML 文件的模板代码（文本必须是预转义的 XML）：
```bash
python scripts/comment.py unpacked/ 0 "Comment text with &amp; and &#x2019;"
python scripts/comment.py unpacked/ 1 "Reply text" --parent 0  # 回复批注 0
python scripts/comment.py unpacked/ 0 "Text" --author "Custom Author"  # 自定义作者名
```
然后在 document.xml 中添加标记（参见 XML 参考中的批注部分）。

### 步骤 3：打包
```bash
python scripts/office/pack.py unpacked/ output.docx --original document.docx
```
执行验证并自动修复、压缩 XML、生成 DOCX。使用 `--validate false` 可跳过验证。

**自动修复可以修复的问题：**
- `durableId` >= 0x7FFFFFFF（重新生成有效 ID）
- `<w:t>` 元素中缺少 `xml:space="preserve"`（当存在空白字符时）

**自动修复无法修复的问题：**
- XML 格式错误、无效的元素嵌套、缺失的关系、架构违规

### 常见陷阱

- **替换整个 `<w:r>` 元素**：添加修订时，将整个 `<w:r>...</w:r>` 块替换为并列的 `<w:del>...<w:ins>...`。不要在 run 内部注入修订标签。
- **保留 `<w:rPr>` 格式**：将原始 run 的 `<w:rPr>` 块复制到修订 run 中，以保持粗体、字号等格式。

---

## XML 参考

### 架构合规性

- **`<w:pPr>` 中的元素顺序**：`<w:pStyle>`、`<w:numPr>`、`<w:spacing>`、`<w:ind>`、`<w:jc>`、`<w:rPr>` 放在最后
- **空白字符**：带有前导/尾随空格的 `<w:t>` 需添加 `xml:space="preserve"`
- **RSID**：必须是 8 位十六进制数（例如 `00AB1234`）

### 修订

**插入：**
```xml
<w:ins w:id="1" w:author="Claude" w:date="2025-01-01T00:00:00Z">
  <w:r><w:t>inserted text</w:t></w:r>
</w:ins>
```

**删除：**
```xml
<w:del w:id="2" w:author="Claude" w:date="2025-01-01T00:00:00Z">
  <w:r><w:delText>deleted text</w:delText></w:r>
</w:del>
```

**在 `<w:del>` 内部**：使用 `<w:delText>` 代替 `<w:t>`，使用 `<w:delInstrText>` 代替 `<w:instrText>`。

**最小化编辑** — 仅标记实际变更的部分：
```xml
<!-- 将 "30 days" 修改为 "60 days" -->
<w:r><w:t>The term is </w:t></w:r>
<w:del w:id="1" w:author="Claude" w:date="...">
  <w:r><w:delText>30</w:delText></w:r>
</w:del>
<w:ins w:id="2" w:author="Claude" w:date="...">
  <w:r><w:t>60</w:t></w:r>
</w:ins>
<w:r><w:t> days.</w:t></w:r>
```

**删除整个段落/列表项** — 当删除段落中的所有内容时，还需将段落标记标记为已删除，以便与下一段落合并。在 `<w:pPr><w:rPr>` 中添加 `<w:del/>`：
```xml
<w:p>
  <w:pPr>
    <w:numPr>...</w:numPr>  <!-- 列表编号（如果存在） -->
    <w:rPr>
      <w:del w:id="1" w:author="Claude" w:date="2025-01-01T00:00:00Z"/>
    </w:rPr>
  </w:pPr>
  <w:del w:id="2" w:author="Claude" w:date="2025-01-01T00:00:00Z">
    <w:r><w:delText>Entire paragraph content being deleted...</w:delText></w:r>
  </w:del>
</w:p>
```
如果不在 `<w:pPr><w:rPr>` 中添加 `<w:del/>`，接受修订后会留下空段落/列表项。

**拒绝其他作者的插入** — 在其插入内部嵌套删除：
```xml
<w:ins w:author="Jane" w:id="5">
  <w:del w:author="Claude" w:id="10">
    <w:r><w:delText>their inserted text</w:delText></w:r>
  </w:del>
</w:ins>
```

**恢复其他作者的删除** — 在其后添加插入（不要修改其删除标记）：
```xml
<w:del w:author="Jane" w:id="5">
  <w:r><w:delText>deleted text</w:delText></w:r>
</w:del>
<w:ins w:author="Claude" w:id="10">
  <w:r><w:t>deleted text</w:t></w:r>
</w:ins>
```

### 批注

运行 `comment.py`（参见步骤 2）后，在 document.xml 中添加标记。回复批注时，使用 `--parent` 标志并将标记嵌套在父批注内。

**关键：`<w:commentRangeStart>` 和 `<w:commentRangeEnd>` 是 `<w:r>` 的兄弟元素，绝不能放在 `<w:r>` 内部。**

```xml
<!-- 批注标记是 w:p 的直接子元素，绝不能放在 w:r 内部 -->
<w:commentRangeStart w:id="0"/>
<w:del w:id="1" w:author="Claude" w:date="2025-01-01T00:00:00Z">
  <w:r><w:delText>deleted</w:delText></w:r>
</w:del>
<w:r><w:t> more text</w:t></w:r>
<w:commentRangeEnd w:id="0"/>
<w:r><w:rPr><w:rStyle w:val="CommentReference"/></w:rPr><w:commentReference w:id="0"/></w:r>

<!-- 批注 0 包含嵌套的回复批注 1 -->
<w:commentRangeStart w:id="0"/>
  <w:commentRangeStart w:id="1"/>
  <w:r><w:t>text</w:t></w:r>
  <w:commentRangeEnd w:id="1"/>
<w:commentRangeEnd w:id="0"/>
<w:r><w:rPr><w:rStyle w:val="CommentReference"/></w:rPr><w:commentReference w:id="0"/></w:r>
<w:r><w:rPr><w:rStyle w:val="CommentReference"/></w:rPr><w:commentReference w:id="1"/></w:r>
```

### 图片

1. 将图片文件添加到 `word/media/`
2. 在 `word/_rels/document.xml.rels` 中添加关系：
```xml
<Relationship Id="rId5" Type=".../image" Target="media/image1.png"/>
```
3. 在 `[Content_Types].xml` 中添加内容类型：
```xml
<Default Extension="png" ContentType="image/png"/>
```
4. 在 document.xml 中引用：
```xml
<w:drawing>
  <wp:inline>
    <wp:extent cx="914400" cy="914400"/>  <!-- EMU：914400 = 1 英寸 -->
    <a:graphic>
      <a:graphicData uri=".../picture">
        <pic:pic>
          <pic:blipFill><a:blip r:embed="rId5"/></pic:blipFill>
        </pic:pic>
      </a:graphicData>
    </a:graphic>
  </wp:inline>
</w:drawing>
```

---

## 依赖项

- **pandoc**：文本提取
- **docx**：`npm install -g docx`（用于创建新文档）
- **LibreOffice**：PDF 转换（通过 `scripts/office/soffice.py` 自动配置沙盒环境）
- **Poppler**：`pdftoppm` 用于生成图片
