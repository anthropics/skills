---
name: web-artifacts-builder
description: 用于构建精细的多组件 claude.ai HTML 制品的工具套件，基于现代前端 Web 技术（React、Tailwind CSS、shadcn/ui）。适用于需要状态管理、路由或 shadcn/ui 组件的复杂制品，不适用于简单的单文件 HTML/JSX 制品。
license: Complete terms in LICENSE.txt
---

# Web 制品构建器

要构建功能强大的前端 claude.ai 制品，请按以下步骤操作：
1. 使用 `scripts/init-artifact.sh` 初始化前端项目
2. 编辑生成的代码来开发制品
3. 使用 `scripts/bundle-artifact.sh` 将所有代码打包为单个 HTML 文件
4. 向用户展示制品
5. （可选）测试制品

**技术栈**：React 18 + TypeScript + Vite + Parcel（打包）+ Tailwind CSS + shadcn/ui

## 设计与样式指南

非常重要：为避免常见的"AI 模板化风格"，请勿过度使用居中布局、紫色渐变、统一圆角和 Inter 字体。

## 快速开始

### 第一步：初始化项目

运行初始化脚本创建新的 React 项目：
```bash
bash scripts/init-artifact.sh <project-name>
cd <project-name>
```

该脚本会创建一个完整配置的项目，包含：
- ✅ React + TypeScript（基于 Vite）
- ✅ Tailwind CSS 3.4.1 及 shadcn/ui 主题系统
- ✅ 已配置路径别名（`@/`）
- ✅ 40+ 个 shadcn/ui 组件已预装
- ✅ 包含所有 Radix UI 依赖
- ✅ 已配置 Parcel 用于打包（通过 .parcelrc）
- ✅ 兼容 Node 18+（自动检测并锁定 Vite 版本）

### 第二步：开发制品

编辑生成的文件来构建制品。请参阅下方**常见开发任务**获取指导。

### 第三步：打包为单个 HTML 文件

将 React 应用打包为单个 HTML 制品：
```bash
bash scripts/bundle-artifact.sh
```

该命令会生成 `bundle.html` —— 一个包含所有 JavaScript、CSS 和依赖的独立制品文件。此文件可在 Claude 对话中直接作为制品分享。

**前提条件**：项目根目录必须包含 `index.html` 文件。

**脚本执行内容**：
- 安装打包依赖（parcel、@parcel/config-default、parcel-resolver-tspaths、html-inline）
- 创建支持路径别名的 `.parcelrc` 配置
- 使用 Parcel 构建（不生成 source map）
- 使用 html-inline 将所有资源内联到单个 HTML 中

### 第四步：向用户分享制品

最后，在对话中向用户分享打包后的 HTML 文件，以便用户以制品形式查看。

### 第五步：测试/预览制品（可选）

注意：此步骤完全可选。仅在必要时或用户要求时执行。

要测试/预览制品，请使用可用工具（包括其他技能或内置工具如 Playwright 或 Puppeteer）。一般情况下，避免预先测试制品，因为这会增加从请求到展示最终制品之间的延迟。建议在展示制品后，如用户要求或出现问题时再进行测试。

## 参考资料

- **shadcn/ui 组件**：https://ui.shadcn.com/docs/components
