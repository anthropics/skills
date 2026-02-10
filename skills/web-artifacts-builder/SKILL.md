---
name: web-artifacts-builder
description: 用于使用现代前端 web 技术（React、Tailwind CSS、shadcn/ui）创建复杂的多组件 claude.ai HTML 工具套件。用于需要状态管理、路由或 shadcn/ui 组件的复杂工件 - 不适用于简单的单文件 HTML/JSX 工件。
license: 完整条款见 LICENSE.txt
---

# Web 工件构建器

要构建强大的前端 claude.ai 工件，请按照以下步骤操作：
1. 使用 `scripts/init-artifact.sh` 初始化前端仓库
2. 通过编辑生成的代码来开发您的工件
3. 使用 `scripts/bundle-artifact.sh` 将所有代码打包到单个 HTML 文件中
4. 向用户显示工件
5.（可选）测试工件

**技术栈**：React 18 + TypeScript + Vite + Parcel（打包）+ Tailwind CSS + shadcn/ui

## 设计和样式指南

非常重要：为了避免通常被称为"AI 渣滓"的内容，请避免使用过度的居中布局、紫色渐变、统一的圆角和 Inter 字体。

## 快速开始

### 步骤 1：初始化项目

运行初始化脚本以创建新的 React 项目：
```bash
bash scripts/init-artifact.sh <project-name>
cd <project-name>
```

这将创建一个完全配置的项目，具有：
- ✅ React + TypeScript（通过 Vite）
- ✅ Tailwind CSS 3.4.1 和 shadcn/ui 主题系统
- ✅ 配置的路径别名（`@/`）
- ✅ 预装 40+ 个 shadcn/ui 组件
- ✅ 包含所有 Radix UI 依赖项
- ✅ 为打包配置的 Parcel（通过 .parcelrc）
- ✅ Node 18+ 兼容性（自动检测并固定 Vite 版本）

### 步骤 2：开发您的工件

要构建工件，请编辑生成的文件。请参阅下面的**常见开发任务**以获取指导。

### 步骤 3：打包为单个 HTML 文件

要将 React 应用打包为单个 HTML 工件：
```bash
bash scripts/bundle-artifact.sh
```

这将创建 `bundle.html` - 一个自包含的工件，其中所有 JavaScript、CSS 和依赖项都已内联。此文件可以直接在 Claude 对话中作为工件共享。

**要求**：您的项目必须在根目录中有 `index.html`。

**脚本的作用**：
- 安装打包依赖项（parcel、@parcel/config-default、parcel-resolver-tspaths、html-inline）
- 创建支持路径别名的 `.parcelrc` 配置
- 使用 Parcel 构建（无源映射）
- 使用 html-inline 将所有资产内联到单个 HTML 中

### 步骤 4：与用户共享工件

最后，在对话中与用户共享打包的 HTML 文件，以便他们可以将其作为工件查看。

### 步骤 5：测试/可视化工件（可选）

注意：这是一个完全可选的步骤。仅在必要时或被请求时执行。

要测试/可视化工件，请使用可用的工具（包括其他技能或 Playwright 或 Puppeteer 等内置工具）。通常，避免预先测试工件，因为它会在请求和看到完成的工件之间增加延迟。如果被请求或出现问题，请在展示工件后稍后测试。

## 参考

- **shadcn/ui 组件**：https://ui.shadcn.com/docs/components
