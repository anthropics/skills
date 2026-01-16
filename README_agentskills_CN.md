# Agent Skills

面向 AI 编码智能体的一组技能集合。技能是经过打包的说明与脚本，用于扩展智能体的能力。

本仓库的技能遵循 [Agent Skills](https://agentskills.io/) 格式。

## 可用技能

### react-best-practices

来自 Vercel Engineering 的 React 与 Next.js 性能优化指南，包含 8 个类别、40+ 条规则，并按影响程度排序。

**适用场景：**
- 编写新的 React 组件或 Next.js 页面
- 实现数据获取（客户端或服务端）
- 审查代码的性能问题
- 优化包体积或加载时间

**覆盖类别：**
- 消除瀑布流（关键）
- 包体积优化（关键）
- 服务端性能（高）
- 客户端数据获取（中-高）
- 重新渲染优化（中）
- 渲染性能（中）
- JavaScript 微优化（低-中）

### web-design-guidelines

审查 UI 代码是否符合 Web 界面最佳实践。会基于 100+ 条规则对你的代码进行审计，覆盖可访问性、性能与 UX。

**适用场景：**
- "Review my UI"
- "Check accessibility"
- "Audit design"
- "Review UX"
- "Check my site against best practices"

**覆盖类别：**
- 可访问性（aria-labels、语义化 HTML、键盘交互处理）
- 焦点态（可见焦点、focus-visible 模式）
- 表单（autocomplete、校验、错误处理）
- 动画（prefers-reduced-motion、合成器友好 transform）
- 排版（弯引号、省略号、tabular-nums）
- 图片（尺寸、懒加载、alt 文本）
- 性能（虚拟列表、布局抖动、preconnect）
- 导航与状态（URL 反映状态、深链接）
- 暗色模式与主题（color-scheme、theme-color meta）
- 触控与交互（touch-action、tap-highlight）
- 本地化与 i18n（Intl.DateTimeFormat、Intl.NumberFormat）

### vercel-deploy-claimable

将应用和网站即时部署到 Vercel。面向 claude.ai 与 Claude Desktop 设计，可直接在对话中发起部署。部署是“可认领”的（claimable）——用户可以将部署所有权转移到自己的 Vercel 账号。

**适用场景：**
- "Deploy my app"
- "Deploy this to production"
- "Push this live"
- "Deploy and give me the link"

**功能：**
- 从 `package.json` 自动识别 40+ 种框架
- 返回预览 URL（线上站点）与认领 URL（转移所有权）
- 自动处理静态 HTML 项目
- 上传时排除 `node_modules` 与 `.git`

**工作原理：**
1. 将项目打包为 tarball
2. 检测框架（Next.js、Vite、Astro 等）
3. 上传到部署服务
4. 返回预览 URL 和认领 URL

**输出：**
```
Deployment successful!

Preview URL: https://skill-deploy-abc123.vercel.app
Claim URL:   https://vercel.com/claim-deployment?code=...
```

## 安装

```bash
npx add-skill vercel-labs/agent-skills
```

## 使用

安装完成后技能会自动可用。智能体会在检测到相关任务时使用它们。

**示例：**
```
Deploy my app
```
```
Review this React component for performance issues
```
```
Help me optimize this Next.js page
```

## 技能结构

每个技能包含：
- `SKILL.md` - 给智能体的说明
- `scripts/` - 自动化辅助脚本（可选）
- `references/` - 支撑文档（可选）

## 许可证

MIT

