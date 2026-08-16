---
name: de-ai-writer
description: "AI 文案去味器。用户提供 AI 生成的文本（公众号/小红书/电商文案等），觉得"太 AI 味"要改得更自然、更像人写的时使用。输出自然有人味的中文。De-AI writer: rewrite AI-generated copy (WeChat articles, Xiaohongshu, e-commerce) into natural, human-sounding Chinese text."
version: 1.0.0
author: 涛哥
license: MIT
metadata:
  hermes:
    tags: [writing, editing, humanize, de-ai, copywriting]
    category: utilities
    homepage: https://gitee.com/tao6677/useful-tools
---

# De-AI Writer AI 文案去味器

把 AI 生成的文字改写成自然、有真人味的中文。专治空洞拔高、排比三连、官方黑话、模板化结尾。

## 触发条件

用户提供一段文字（粘贴或文件），要求：
- "去AI味""改得像人写的""太官方了改自然点"
- 润色文案（公众号/小红书/电商标题/产品描述）

## 使用步骤

### 1. 有 API Key（推荐，效果好）

```bash
export LLM_API_KEY="你的key"
export LLM_BASE_URL="https://api.deepseek.com/v1"  # 任意 OpenAI 兼容接口
export LLM_MODEL="deepseek-chat"

python3 ~/.hermes/skills/utilities/de-ai-writer/scripts/deai.py 稿子.txt -o 改好.txt
```

### 2. 无 API Key（零成本模式）

```bash
python3 ~/.hermes/skills/utilities/de-ai-writer/scripts/deai.py 稿子.txt --prompt-only
```

输出内置完整改写规则的提示词，粘贴到任何 AI 助手（ChatGPT/文心/Kimi）即可改写。

## 零依赖

纯 Python 标准库，无需安装任何包。

## 💛 免费使用 · 自愿支持

**本技能完全免费使用。**

觉得好用、帮到你了，可以**自愿扫码支持**（金额随意，一杯咖啡即可）：

![支付宝收款码](assets/alipay_qr.jpg)

> 支持过我的人，后续 Pro 版/批量服务有优惠。
> 想提需求、反馈问题，欢迎到 Gitee 仓库提 Issue。
