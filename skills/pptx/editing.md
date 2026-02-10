# 编辑演示文稿

## 基于模板的工作流程

使用现有演示文稿作为模板时：

1. **分析现有幻灯片**：
   ```bash
   python scripts/thumbnail.py template.pptx
   python -m markitdown template.pptx
   ```
   查看 `thumbnails.jpg` 以了解布局，以及 markitdown 输出以查看占位符文本。

2. **规划幻灯片映射**：对于每个内容部分，选择一个模板幻灯片。

   ⚠️ **使用多样化布局** — 单调的演示文稿是一种常见的失败模式。不要默认使用基本的标题 + 项目符号幻灯片。积极寻找：
   - 多栏布局（2 栏、3 栏）
   - 图像 + 文本组合
   - 带文本叠加的全出血图像
   - 引用或标注幻灯片
   - 章节分隔符
   - 统计/数字标注
   - 图标网格或图标 + 文本行

   **避免：** 为每张幻灯片重复相同的重度文本布局。

   将内容类型与布局样式匹配（例如，关键点 → 项目符号幻灯片，团队信息 → 多栏，推荐语 → 引用幻灯片）。

3. **解包**：`python scripts/office/unpack.py template.pptx unpacked/`

4. **构建演示文稿**（自己完成，不使用子代理）：
   - 删除不需要的幻灯片（从 `<p:sldIdLst>` 中删除）
   - 复制要重复使用的幻灯片（`add_slide.py`）
   - 在 `<p:sldIdLst>` 中重新排序幻灯片
   - **在步骤 5 之前完成所有结构更改**

5. **编辑内容**：更新每个 `slide{N}.xml` 中的文本。
   **如果有可用子代理，请在此处使用** — 幻灯片是单独的 XML 文件，因此子代理可以并行编辑。

6. **清理**：`python scripts/clean.py unpacked/`

7. **打包**：`python scripts/office/pack.py unpacked/ output.pptx --original template.pptx`

---

## 脚本

| 脚本 | 目的 |
|--------|---------|
| `unpack.py` | 提取并美化打印 PPTX |
| `add_slide.py` | 复制幻灯片或从布局创建 |
| `clean.py` | 删除孤立文件 |
| `pack.py` | 带验证重新打包 |
| `thumbnail.py` | 创建幻灯片视觉网格 |

### unpack.py

```bash
python scripts/office/unpack.py input.pptx unpacked/
```

提取 PPTX，美化打印 XML，转义智能引号。

### add_slide.py

```bash
python scripts/add_slide.py unpacked/ slide2.xml      # 复制幻灯片
python scripts/add_slide.py unpacked/ slideLayout2.xml # 从布局
```

打印 `<p:sldId>` 以在所需位置添加到 `<p:sldIdLst>`。

### clean.py

```bash
python scripts/clean.py unpacked/
```

删除不在 `<p:sldIdLst>` 中的幻灯片、未引用的媒体、孤立的关系。

### pack.py

```bash
python scripts/office/pack.py unpacked/ output.pptx --original input.pptx
```

验证、修复、压缩 XML、重新编码智能引号。

### thumbnail.py

```bash
python scripts/thumbnail.py input.pptx [output_prefix] [--cols N]
```

创建带有幻灯片文件名作为标签的 `thumbnails.jpg`。默认 3 列，每个网格最多 12 张。

**仅用于模板分析**（选择布局）。对于视觉 QA，使用 `soffice` + `pdftoppm` 创建全分辨率单独幻灯片图像 — 请参阅 SKILL.md。

---

## 幻灯片操作

幻灯片顺序位于 `ppt/presentation.xml` → `<p:sldIdLst>`。

**重新排序**：重新排列 `<p:sldId>` 元素。

**删除**：删除 `<p:sldId>`，然后运行 `clean.py`。

**添加**：使用 `add_slide.py`。永远不要手动复制幻灯片文件 — 该脚本处理注释引用、Content_Types.xml 和手动复制会遗漏的关系 ID。

---

## 编辑内容

**子代理**：如果有可用，请在此处使用（完成步骤 4 后）。每个幻灯片都是一个单独的 XML 文件，因此子代理可以并行编辑。在您给子代理的提示中，包括：
- 要编辑的幻灯片文件路径
- **"对所有更改使用编辑工具"**
- 以下格式规则和常见陷阱

对于每张幻灯片：
1. 阅读幻灯片的 XML
2. 识别所有占位符内容 — 文本、图像、图表、图标、说明文字
3. 将每个占位符替换为最终内容

**使用编辑工具，而不是 sed 或 Python 脚本。** 编辑工具强制指定要替换的内容和位置，从而产生更好的可靠性。

### 格式规则

- **加粗所有标题、副标题和内联标签**：在 `<a:rPr>` 上使用 `b="1"`。这包括：
  - 幻灯片标题
  - 幻灯片内的章节标题
  - 行首的内联标签（例如："状态："、"描述："）
- **永远不要使用 unicode 项目符号（•）**：使用带有 `<a:buChar>` 或 `<a:buAutoNum>` 的正确列表格式
- **项目符号一致性**：让项目符号从布局继承。仅指定 `<a:buChar>` 或 `<a:buNone>`。

---

## 常见陷阱

### 模板适应

当源内容的项目少于模板时：
- **完全删除多余的元素**（图像、形状、文本框），而不仅仅是清除文本
- 清除文本内容后检查孤立的视觉效果
- 运行视觉 QA 以捕捉不匹配的计数

当用不同长度的内容替换文本时：
- **较短的替换**：通常安全
- **较长的替换**：可能会溢出或意外换行
- 文本更改后进行视觉 QA
- 考虑截断或拆分内容以适应模板的设计约束

**模板槽 ≠ 源项目**：如果模板有 4 个团队成员但源有 3 个用户，请删除第 4 个成员的整个组（图像 + 文本框），而不仅仅是文本。

### 多项目内容

如果源有多个项目（编号列表、多个章节），为每个项目创建单独的 `<a:p>` 元素 — **永远不要连接成一个字符串**。

**❌ 错误** — 一个段落中的所有项目：
```xml
<a:p>
  <a:r><a:rPr .../><a:t>第 1 步：做第一件事。第 2 步：做第二件事。</a:t></a:r>
</a:p>
```

**✅ 正确** — 带有加粗标题的独立段落：
```xml
<a:p>
  <a:pPr algn="l"><a:lnSpc><a:spcPts val="3919"/></a:lnSpc></a:pPr>
  <a:r><a:rPr lang="en-US" sz="2799" b="1" .../><a:t>第 1 步</a:t></a:r>
</a:p>
<a:p>
  <a:pPr algn="l"><a:lnSpc><a:spcPts val="3919"/></a:lnSpc></a:pPr>
  <a:r><a:rPr lang="en-US" sz="2799" .../><a:t>做第一件事。</a:t></a:r>
</a:p>
<a:p>
  <a:pPr algn="l"><a:lnSpc><a:spcPts val="3919"/></a:lnSpc></a:pPr>
  <a:r><a:rPr lang="en-US" sz="2799" b="1" .../><a:t>第 2 步</a:t></a:r>
</a:p>
<!-- 继续模式 -->
```

从原始段落复制 `<a:pPr>` 以保留行间距。在标题上使用 `b="1"`。

### 智能引号

由 unpack/pack 自动处理。但编辑工具会将智能引号转换为 ASCII。

**添加带引号的新文本时，使用 XML 实体：**

```xml
<a:t> &#x201C;协议&#x201D;</a:t>
```

| 字符 | 名称 | Unicode | XML 实体 |
|-----------|------|---------|------------|
| `"`` | 左双引号 | U+201C | `&#x201C;` |
| `"` | 右双引号 | U+201D | `&#x201D;` |
| `'` | 左单引号 | U+2018 | `&#x2018;` |
| `'` | 右单引号 | U+2019 | `&#x2019;` |

### 其他

- **空白**：在带有前导/尾随空格的 `<a:t>` 上使用 `xml:space="preserve"`
- **XML 解析**：使用 `defusedxml.minidom`，而不是 `xml.etree.ElementTree`（破坏命名空间）
