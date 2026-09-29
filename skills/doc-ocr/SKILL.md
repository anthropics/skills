---
name: doc-ocr
description: "文档文字识别。用户提供 PDF/扫描件/图片（合同、发票、书页、截图），需要提取文字、转成可编辑文本时使用。扫描件自动 OCR（macOS Vision，中英文）。Document OCR: extract editable text from PDFs, scans, and images (contracts, invoices, book pages, screenshots) via macOS Vision."
version: 1.0.0
author: 涛哥
license: MIT
metadata:
  hermes:
    tags: [ocr, pdf, document, text-extraction, scan]
    category: utilities
    homepage: https://gitee.com/tao6677/useful-tools
---

# Doc-OCR 文档文字识别

PDF / 扫描件 / 图片 → 可编辑文字。有文字层的 PDF 直接提取，扫描件自动 OCR（macOS Vision 自带，中英文）。

## 触发条件

用户提供 PDF/图片文件，要求：
- "提取文字""转文字""OCR"
- 处理扫描件、合同、发票、书页、截图

## 使用步骤

### 1. 单个文件

```bash
python3 ~/.hermes/skills/utilities/doc-ocr/scripts/dococr.py 合同.pdf
python3 ~/.hermes/skills/utilities/doc-ocr/scripts/dococr.py 发票.jpg
```

输出保存为 `<输入名>_ocr.txt`。

### 2. 批量目录

```bash
python3 ~/.hermes/skills/utilities/doc-ocr/scripts/dococr.py ./扫描件/ -o 全部.txt
```

### 3. Markdown 输出

```bash
python3 ~/.hermes/skills/utilities/doc-ocr/scripts/dococr.py 书.pdf --md
```

## 依赖（首次使用时安装）

```bash
pip3 install pymupdf pyobjc-framework-Vision
```

**注意**：OCR 依赖 macOS Vision（仅 macOS 可用）。Linux 需另装 tesseract 等引擎。

## 已知陷阱

- **扫描件判定**：PDF 文字层 <20 字自动走 OCR，正常 PDF 直接提取。
- **手写体**：Vision 对印刷体/清晰手写效果好，潦草手写不保证。
- **隐私卖点**：文件在本机处理，不上传第三方。

## 💛 免费使用 · 自愿支持

**本技能完全免费使用。**

觉得好用、帮到你了，可以**自愿扫码支持**（金额随意，一杯咖啡即可）：

![支付宝收款码](assets/alipay_qr.jpg)

> 支持过我的人，后续 Pro 版/批量服务有优惠。
> 想提需求、反馈问题，欢迎到 Gitee 仓库提 Issue。
