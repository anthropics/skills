# Structured Learning Skill

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![GitHub Stars](https://img.shields.io/github/stars/GlacierXiaowei/structured-learning-skill?style=social)](https://github.com/GlacierXiaowei/structured-learning-skill)
[![Install](https://img.shields.io/badge/Install-npx%20skills%20add-green)](https://skills.sh/skill/glacierxiaowei/structured-learning)

> **The first AI teaching skill with dual-mode switching** 🎓
> 
> Concise mode for quick review, detailed 7-step mode for systematic learning. Auto-adapts to your setup (MCP/File/Context). Ideal for academic subjects and exam preparation.

English | [简体中文](./structured-learning/README.md)

---

## ✨ Key Features

| Feature | Description |
|---------|-------------|
| **Dual-Mode Teaching** | 3-step concise mode / 7-step detailed mode |
| **Three-Tier User Adaptation** | Advanced (MCP) / Intermediate (File) / Basic (Context) |
| **Structured Thinking** | Auto-detect MCP or use embedded reasoning |
| **Exam-Oriented** | Exam highlights, question templates, answer standards |
| **Personalized Memory** | Knowledge tracking, error recording, mode preferences |

---

## 📦 Installation

### Claude Code / OpenCode

```bash
# Method 1: Copy to skills directory
mkdir -p ~/.config/opencode/skills/structured-learning
cp SKILL.md ~/.config/opencode/skills/structured-learning/SKILL.md

# Method 2: Install from skills.sh
npx skills add glacierxiaowei/structured-learning
```

### Cursor

```bash
# Create cursor rules directory
mkdir -p .cursor/rules

# Download the skill
curl -o .cursor/rules/structured-learning.mdc https://raw.githubusercontent.com/GlacierXiaowei/structured-learning-skill/main/.cursor/rules/structured-learning.mdc
```

### Windsurf

```bash
# Create .windsurfrules in project root
curl -o .windsurfrules https://raw.githubusercontent.com/GlacierXiaowei/structured-learning-skill/main/.windsurfrules
```

### GitHub Copilot

```bash
mkdir -p .github
curl -o .github/copilot-instructions.md https://raw.githubusercontent.com/GlacierXiaowei/structured-learning-skill/main/.github/copilot-instructions.md
```

---

## 🚀 Quick Start

### Trigger Examples

```
User: 讲一下偏导数
User: 帮我复习一下等值演算
User: 详细讲一下主范式
User: 离散数学期末要考什么
```

### Mode Switching

```
User: 详细模式 / 详细讲 / 展开讲讲
User: 简明模式 / 简单说 / 直接给答案
User: 举个例子 / 给道题
User: 不懂 / 没明白
```

### Works with Guided Learning

```
User: 这道题怎么做：求 f(x) = x² + 2x 的最小值
AI: [Short answer] + 💡 Say: 使用引导式学习
User: 使用引导式学习
AI: [Socratic guidance]
```

---

## 📖 Documentation

- [Full README (Chinese)](./structured-learning/README.md)
- [SKILL.md](./SKILL.md) - Complete skill instructions
- [Design Document](./structured-learning/交接提示词.md)

---

## 🎯 Use Cases

| Scenario | Mode | Example |
|----------|------|---------|
| Quick review | Concise | "复习一下偏导数" |
| Learn new concept | Detailed | "详细讲一下主范式" |
| Exam preparation | Detailed | "离散数学期末要考什么" |
| Definition lookup | Concise | "什么是等值演算" |
| Concept confusion | Detailed | "没明白，再讲一次" |

---

## 🔧 Platform Support

| Platform | Support | Install Method |
|----------|---------|----------------|
| Claude Code | ✅ Full | Copy to `~/.config/opencode/skills/` |
| OpenCode | ✅ Full | Same as Claude Code |
| Cursor | ✅ Full | `.cursor/rules/structured-learning.mdc` |
| Windsurf | ✅ Full | `.windsurfrules` |
| GitHub Copilot | ✅ Full | `.github/copilot-instructions.md` |
| skills.sh | ✅ Available | `npx skills add glacierxiaowei/structured-learning` |

---

## 🤝 Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](./CONTRIBUTING.md) for details.

---

## 📄 License

Apache License 2.0 - see [LICENSE](./LICENSE) for details.

---

## 👤 Author

**冰川小未（魏子杰）**
- School: Tianjin University, Computer Science
- GitHub: [@GlacierXiaowei](https://github.com/GlacierXiaowei)

---

## 🙏 References

- [Gemini Guided Learning](https://blog.google/products/gemini/guided-learning-google-gemini/)
- [anthropics/skills](https://github.com/anthropics/skills)
- [writing-skills skill specification](https://github.com/anthropics/skills/tree/main/skills/skill-creator)