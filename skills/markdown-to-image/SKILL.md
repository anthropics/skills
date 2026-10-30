---
name: markdown-to-image
description: Use when user wants to convert Markdown content into shareable image cards — triggered by phrases like "转图片"、"做卡片"、"生成海报"、"生成分享图"、"把这个转成图片"、"export as image". Applies to any .md file or inline Markdown content destined for WeChat, Xiaohongshu, Weibo, or similar platforms.
---

# Markdown → 图片卡片

将 Markdown 渲染为多张精美图片，适合社交平台分享。

## 核心原则

**不要询问用户任何参数。直接执行。**

所有选项均有合理默认值；只有用户主动提出才切换。

## 执行流程

### 步骤 0：预检查（必须，在生成前执行）

读取完整 Markdown 文件，检查以下问题：

**技术问题**
- ChatGPT 引用标记：文件含 `citeturnXviewY` 或 Unicode 私用区字符（U+E000–U+F8FF）
- 编码异常、乱码字符

**内容问题**
- 开头有无关内容（如导出说明、来源标注、平台水印文字）
- 结尾有无关内容（如参考文献列表、脚注、版权声明、"以上内容由AI生成"等）
- 大段重复或明显不适合做成卡片的内容

**格式问题**
- 标题层级混乱（如多个 H1、层级跳跃）
- 表格格式错误

**判断规则：**
- 如果发现任何问题 → 向用户列出问题摘要，询问"是否修复后再生成？"
- 如果文件干净 → 直接进入步骤 1，不打扰用户

**修复 ChatGPT 引用标记的方法：**
```python
import re
with open('input.md', 'r', encoding='utf-8') as f:
    content = f.read()
cleaned = re.sub(r'cite(\w+)*', '', content)
cleaned = re.sub(r'[-]', '', cleaned)
cleaned = re.sub(r'cite\w+', '', cleaned)
with open('input_clean.md', 'w', encoding='utf-8') as f:
    f.write(cleaned)
```

### 步骤 1：确定标题

读文件前 30 行，理解主题，起 4-8 字书名式标题：
- ✅ `摔PS5惩罚分析` / `AI提问艺术` / `AI时代儿童成长路线图`
- ❌ `心理学与教育学的专业共识认为母亲用同态报`

### 步骤 2：生成图片（含封面标题卡）

```bash
node ~/.claude/skills/markdown-to-image/src/index.js \
  --markdown "/path/to/file.md" \
  --title "卡片标题" \
  --name "卡片标题"
```

`--title` 会生成封面卡（`-00.png`），内容卡从 `-01.png` 开始。

输出自动写入 `~/Downloads/<卡片名>/`。

## 默认值（不传即生效）

| 参数 | 默认 |
|------|------|
| `--theme` | `white`（简约白） |
| `--page-format` | `total`（01 / 12） |
| `--output` | `~/Downloads/<卡片名>/` |

## 主题速查

| `--theme` | 中文名 | 适合场景 |
|-----------|--------|---------|
| `white` | 简约白 ★默认 | 通用、正式 |
| `dark` | 深色模式 | 科技、夜间风 |

## 页码格式

```bash
--page-format default    # 01, 02, 03
--page-format total      # 01 / 12, 02 / 12  ← 默认
--page-format brackets   # (1/12), (2/12)
```

## 常见错误

| 错误 | 正确做法 |
|------|---------|
| 跳过预检查直接生成 | 必须先读文件检查，有问题再问用户 |
| 询问用户要哪个主题 | 直接用 `white`，完成后可提示切换 |
| 用文件名乱码当卡片名 | 读内容，自己起标题 |
| 手动传 `--output` | 省略，自动输出到 Downloads |
| 截句子当标题 | 起书名式短标题（4-8 字） |
| 不传 `--title` | 总是传 `--title`，生成封面卡 |
