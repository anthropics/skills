# Framer / Anima / Locofy — D2C 对照摘要

> 来源：公开搜索与官网/文档摘要；获取日期 2026-03-04

## Framer

- **D2C 定位**：Framer 官方**不提供**设计稿导出为 HTML/CSS/JS 或 React 代码；产品为闭环建站与托管，依赖内部运行时。
- **第三方**：ConvertFramer 等提供「Framer → React/Next.js」付费转换（如按页收费），导出为可读 React 组件；官方有 plugins-code-file-exports 等开发者能力，但非面向「设计稿一键转代码」。
- **与 Figma 差异**：Figma 以「设计文件 + Dev Mode 检查 + 代码片段/Code Connect」为主；Framer 以「在 Framer 内设计并发布」为主，代码导出为补充或第三方能力。

## Anima

- **定位**：AI 驱动、Figma → 生产级代码，支持 React、HTML、Vue、CSS（Tailwind、Styled Components、SCSS 等）及 MUI、Ant Design、Shadcn 等组件库。
- **使用方式**：Figma 插件（推荐）或 Anima Playground 粘贴 Figma 链接；支持在 **Figma Dev Mode** 内集成，便于开发交接。
- **特点**：Auto layout → Flexbox/Grid、多屏与设计系统导出、可推 GitHub 或复制片段；「Vibe coding」为 AI 微调生成代码。

## Locofy

- **定位**：AI 设计转代码（Large Design Models），Figma 插件「Locofy Lightning」支持一键转换；强调 pixel-perfect、高质量前端代码。
- **输出**：响应式 HTML/CSS、支持多断点、数据绑定与后端 API 对接；企业级部署选项（SaaS/ Dedicated/ Private Cloud/ On-Premise）。
- **流程**：Figma 设计 → 实时预览 → 生成代码；支持 GitHub 同步、组件标记与图层命名。

## 与 Figma 官方 D2C 的对比要点

| 维度 | Figma Dev Mode | Anima | Locofy | Framer |
|------|----------------|-------|--------|--------|
| 代码来源 | 官方多语言片段 + Code Connect 真实代码 | 插件生成 React/HTML/Vue 等 | 插件 AI 生成 HTML/CSS 等 | 官方不导出，第三方转换 |
| 与设计文件关系 | 同文件内 Inspect，只读 | 插件在 Figma 内，可接 Dev Mode | 插件在 Figma 内 | 独立产品，非 Figma |
| 设计系统 | Code Connect 连代码库 | 支持 MUI/Ant/Shadcn 等 | 组件与命名驱动 | N/A |
