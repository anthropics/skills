# markdown-to-image

将 Markdown 文件渲染为多张图片卡片，适合微信、小红书、微博等社交平台分享。

## 特性

- 自动分页，按内容高度精确切割
- 支持标题、正文、列表、代码块、表格、引用、图片、Mermaid 图表
- 长列表 / 长表格跨页自动拆分
- 孤立标题自动移至下一页（不产生纯标题页）
- 远程图片自动下载；GIF 跳过
- 字体：PingFang SC（macOS）→ Noto Sans SC（跨平台）→ Microsoft YaHei
- 两套主题：`white`（默认）/ `dark`

## 环境要求

- Node.js 18+
- Google Chrome（路径：`/Applications/Google Chrome.app`，macOS）
- 网络连接（首次生成时加载 Noto Sans SC 字体）

## 安装

```bash
npm install
```

## 使用

```bash
node src/index.js \
  --markdown "/path/to/file.md" \
  --title  "封面标题" \
  --name   "卡片名称"
```

输出自动写入 `~/Downloads/<卡片名称>/`，文件命名为 `<名称>-00.png`（封面）、`-01.png`、`-02.png`……

### 参数

| 参数 | 说明 | 默认值 |
|------|------|--------|
| `--markdown <file>` | Markdown 文件路径 | — |
| `--title <text>` | 封面标题（生成 `-00.png`） | — |
| `--name <text>` | 输出文件名前缀 | 自动从文件内容提取 |
| `--theme <name>` | 主题：`white` / `dark` | `white` |
| `--page-format <style>` | 页码格式（见下） | `total` |
| `--output <dir>` | 自定义输出目录 | `~/Downloads/<名称>/` |

### 页码格式

| `--page-format` | 示例 |
|-----------------|------|
| `default` | `01` |
| `total` ★ | `01 / 12` |
| `brackets` | `(1/12)` |

## 主题

| `--theme` | 说明 |
|-----------|------|
| `white` | 简约白，默认 |
| `dark` | 深色模式 |

主题配置在 `src/themes.js`，可调整：背景色、文字色、代码块背景、边框色、强调色、字体、间距、圆角。

## 支持的 Markdown 语法

| 语法 | 说明 |
|------|------|
| `# H1` `## H2` `### H3` | 三级标题 |
| `**bold**` `*italic*` | 加粗 / 斜体 |
| `` `code` `` | 行内代码 |
| ` ```code block``` ` | 代码块（自动缩小超长块） |
| ` ```mermaid``` ` | Mermaid 图表（流程图等） |
| `- item` / `1. item` | 无序 / 有序列表（超长自动跨页） |
| `> quote` | 引用块 |
| `| table |` | 表格（超长自动跨页） |
| `![alt](path)` | 本地图片 / 远程图片（自动下载） |

## 卡片规格

| 属性 | 值 |
|------|----|
| 尺寸 | 1440 × 2400 px |
| 内容区宽度 | 1200 px（左右各 120 px 内边距） |
| 内容区高度 | 最大 2060 px |
| 基础字号 | 48 px（正文）|
| 代码字号 | 42 px（超长块自动缩至 32 px）|

## 项目结构

```
src/
├── index.js            # CLI 入口，参数解析
├── generator.js        # 核心：浏览器控制、分页、截图
├── markdown-parser.js  # Markdown → 内容块（支持图片下载）
├── paginator.js        # 标题字号计算（封面卡用）
├── themes.js           # 主题定义
└── templates/
    ├── mixed-content-card.html  # 内容卡模板
    └── title-card.html          # 封面卡模板
```

## 分页逻辑

1. 将 Markdown 解析为独立内容块（标题 / 段落 / 列表 / 表格 / 代码块 / 图片 / Mermaid）
2. 用 Puppeteer 在无头浏览器里实际渲染并测量每块高度
3. 贪心装箱：逐块尝试加入当前页，超出则换页
4. 超长列表 / 表格：二分查找可放入的最大行数后拆分
5. 孤立标题修复：末尾全是标题 → 移至下一页；整页全是标题 → 从下页借一块
