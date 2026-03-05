# Figma Dev Mode — D2C 设计调研摘要

> 来源：figma.com/dev-mode、help.figma.com Guide to Dev Mode、developers.figma.com；获取日期 2026-03-04

## 1. 定位与准入

- **定位**：面向开发者的只读界面，用于「inspect designs and translate them into code」且不修改设计文件。
- **准入**：所有付费计划下的 **Full** 或 **Dev** 席位；免费计划不可用。

## 2. 结构层 · 任务流与角色

- **入口**：在设计文件中通过 **Dev Mode 切换**（或快捷键 Shift+D）进入；也可通过 Dev Mode 链接打开时直接进入。
- **设计师**：在 Design Mode 中标记 frame/component/instance/section 为「Ready for dev」；可加标注、测量、状态。
- **开发**：在 Dev Mode 中查看「Ready for development」列表、Focus view 单帧、版本对比、Inspect 面板取标注与代码。
- **协作**：状态（Ready for dev / Completed）、通知（设计被标为 ready 时通知开发）、评论与注解贯穿流程。

## 3. 框架层 · 信息与能力组织

- **左侧**：按 Section 组织的导航；可只看「Ready for dev」；显示 frame 最后编辑时间。
- **Inspect 面板**：图层名与类型、Compare changes、外部链接（GitHub/Jira/Storybook/VS Code）、组件信息与 **Component playground**（变体与属性）、**Code Connect**（连接代码库后展示真实组件代码）、图层属性（Code/List 切换）、样式与变量、资源下载、导出设置。
- **代码片段**：支持多语言（CSS、Compose、XML、SwiftUI、UIKit 等）、单位（rem/px）、codegen 插件扩展；Code Connect 下可显示设计系统真实代码而非仅自动生成。

## 4. 表现层 · 交互与衔接

- **Figma for VS Code**：在编辑器内浏览与 inspect 文件、链接代码与设计、基于设计给代码建议、实时评论与动态。
- **Figma MCP Server**：将 Figma 上下文带入 Cursor、Claude、Windsurf 等，支持基于设计的代码生成。
- **Code Connect**：设计系统组件与代码库映射，Organization/Enterprise 可用；支持 React、SwiftUI、Jetpack Compose、HTML 等。

## 5. 与插件生态的边界

- 官方提供 **Inspect + 多语言代码片段 + Code Connect**；自定义语言/框架依赖 **Dev Mode 插件**（如 Tailwind、自定义 React 组件）。
- 社区插件可扩展代码输出、对接 GitHub/Storybook/Jira，与 Dev Mode 内 Plugins  tab 整合。
