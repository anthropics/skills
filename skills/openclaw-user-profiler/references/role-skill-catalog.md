# 角色 × Skill 推荐目录

根据用户角色推荐适合的 Claude Code Skill。覆盖 11 大类 42 个职业角色。

## 推荐原则

1. **精不贪多**：每个角色推荐 5-10 个专属 Skill（不含继承的通用/大类 Skill）
2. **说清为什么**：每条推荐附一句话说明为什么这个角色需要它
3. **继承模型**：通用 → 大类 → 专属，展示时只列专属，继承声明不重复
4. **区分来源**：外部 = skills.sh 安装 / 官方 = Anthropic example-skills

## 来源图例

| 标记 | 含义 | 安装方式 |
|------|------|---------|
| 🅰️ 官方 | Anthropic example-skills | Claude Code 自带 |
| 📦 外部 | skills.sh 社区 Skill | `npx skills add <包名>` |

---

## Level 0：通用 Skill（所有角色自动继承）

| Skill | 来源 | 为什么所有人都需要 |
|-------|------|-------------------|
| brainstorming | 📦 sickn33/antigravity-awesome-skills | 任何创造性工作的起点——头脑风暴、需求探索 |
| planner | 📦 am-will/codex-skills | 任何非平凡任务都需要方案设计和任务拆解 |
| baoyu-image-gen | 📦 jimliu/baoyu-skills | AI 生图，支持 OpenAI/Google/DashScope 多 API（13.3K 安装） |
| baoyu-infographic | 📦 jimliu/baoyu-skills | 专业信息图生成，20 种布局 × 17 种风格（11.2K 安装） |
| find-skills | 📦 vercel-labs/skills | 发现和安装新的 Claude Code Skill |

---

## A. 工程技术类

### Level 1：工程通用（所有工程角色自动继承）

| Skill | 来源 | 为什么工程师都需要 |
|-------|------|-------------------|
| tdd:test-driven-development | 📦 neolabhq/context-engineering-kit | 写代码前先写测试，工程纪律基础 |
| systematic-debugging | 📦 obra/superpowers | 结构化排查 bug，不靠直觉 |
| verification-before-completion | 📦 sickn33/antigravity-awesome-skills | 完工前跑验证，防止遗漏 |
| code-reviewer | 📦 alirezarezvani/claude-skills | 主动请求代码审查，提升代码质量 |
| pr-review-expert | 📦 alirezarezvani/claude-skills | 收到 review 后的处理流程 |
| conventional-commit | 📦 github/awesome-copilot | 规范化 Git 提交 |
| api-documentation-generator | 📦 sickn33/antigravity-awesome-skills | 自动生成 API 文档 |
| github-search | 📦 parcadei/continuous-claude-v3 | GitHub 代码搜索 |
| changelog-maintenance | 📦 supercent-io/skills-template | 自动维护 CHANGELOG，10.9K 安装 |

---

### A1. 后端工程师（Backend Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合后端 |
|-------|------|--------------|
| jenkins-deploy | 📦 abcfed/claude-marketplace | Jenkins 测试环境发布管理 |
| performance-profiling | 📦 sickn33/antigravity-awesome-skills | 服务端性能分析和优化（424 安装） |
| postgresql-database-engineering | 📦 manutej/luxor-claude-marketplace | PostgreSQL 工程实践（442 安装） |
| microservices-architect | 📦 jeffallan/claude-skills | 微服务架构设计指南（977 安装） |
| docker | 📦 bobmatnyc/claude-mpm-skills | Docker 容器化最佳实践（456 安装） |

**按技术栈可选**：

| 技术栈 | Skill | 来源 | 安装量 |
|--------|-------|------|--------|
| Java / Spring | java-springboot | 📦 github/awesome-copilot | 9.1K |
| Python / Django | django-cloud-sql-postgres | 📦 jezweb/claude-skills | 277 |
| Python / Flask | flask | 📦 bobmatnyc/claude-mpm-skills | 129 |
| Go | golang-backend-development | 📦 manutej/luxor-claude-marketplace | 524 |
| Rust | rust-pro | 📦 sickn33/antigravity-awesome-skills | 187 |

---

### A2. 前端工程师（Frontend Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合前端 |
|-------|------|--------------|
| frontend-design | 🅰️ Anthropic 官方 | 高质量 UI 组件生成，避免 AI 审美 |
| webapp-testing | 🅰️ Anthropic 官方 | Playwright 自动化测试本地 Web 应用 |
| web-artifacts-builder | 🅰️ Anthropic 官方 | 复杂多组件 Web Artifact 构建 |
| theme-factory | 🅰️ Anthropic 官方 | 主题/风格系统，10 个预设主题 |
| seo | 📦 addyosmani/web-quality-skills | Google 工程师出品的 SEO 审计（4.2K 安装） |
| accessibility | 📦 addyosmani/web-quality-skills | WCAG 无障碍合规审计（3.9K 安装） |
| nextjs-react-typescript | 📦 mindrally/skills | Next.js + React + TS 最佳实践（1.2K 安装） |
| playwright-testing | 📦 alinaqi/claude-bootstrap | Playwright E2E 测试框架（415 安装） |

---

### A3. 全栈工程师（Full-Stack Engineer）

> 继承：A1（后端）+ A2（前端）全部

全栈工程师是后端和前端的并集，无额外专属 Skill。根据实际技术栈从 A1 和 A2 中选择。

---

### A4. 移动端工程师（Mobile Developer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合移动端 |
|-------|------|----------------|
| react-native | 📦 alinaqi/claude-bootstrap | React Native 流式内容块渲染 |
| frontend-design | 🅰️ Anthropic 官方 | 移动端 UI 组件设计 |
| senior-mobile | 📦 borghei/claude-skills | 移动端高级开发实践（270 安装） |

---

### A5. AI/ML 工程师（AI/ML Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合 AI/ML |
|-------|------|-----------------|
| senior-prompt-engineer | 📦 davila7/claude-code-templates | Claude API / Anthropic SDK 开发 |
| mcp-builder | 🅰️ Anthropic 官方 | 构建 MCP 服务器，集成外部服务 |
| mcp-builder（社区版） | 📦 mcp-use/skills | MCP 服务器构建（299 安装） |
| ml-model-training | 📦 aj-geddes/useful-ai-prompts | ML 模型训练指南（135 安装） |
| ai-ml-data-science | 📦 vasilyu1983/ai-agents-public | AI/ML/数据科学全栈指南（120 安装） |
| news-summary | 📦 sundial-org/awesome-openclaw-skills | AI 资讯日报，追踪最新论文和模型 |
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 总结 AI 论文/讲座/播客 |
| xlsx | 🅰️ Anthropic 官方 | 数据处理和实验结果分析 |

---

### A6. 数据工程师（Data Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合数据工程 |
|-------|------|------------------|
| postgresql-database-engineering | 📦 manutej/luxor-claude-marketplace | PostgreSQL 工程实践（442 安装） |
| sqlite-database-expert | 📦 martinholovsky/claude-skills-generator | SQLite 数据库专家（673 安装） |
| xlsx | 🅰️ Anthropic 官方 | 数据处理和转换 |
| pdf | 🅰️ Anthropic 官方 | PDF 数据提取 |
| ci-cd-best-practices | 📦 mindrally/skills | 数据管道 CI/CD 实践（341 安装） |

---

### A7. 测试工程师（QA Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合测试 |
|-------|------|--------------|
| webapp-testing | 🅰️ Anthropic 官方 | Playwright 自动化测试 |
| playwright-testing | 📦 alinaqi/claude-bootstrap | Playwright E2E 测试（415 安装） |
| performance-profiling | 📦 sickn33/antigravity-awesome-skills | 性能测试和分析（424 安装） |
| docx | 🅰️ Anthropic 官方 | 测试报告撰写 |
| accessibility | 📦 addyosmani/web-quality-skills | 无障碍测试（3.9K 安装） |

---

### A8. 安全工程师（Security Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合安全 |
|-------|------|--------------|
| dependency-vulnerability-checker | 📦 jeremylongshore/claude-code-plugins-plus-skills | 依赖漏洞检查（41 安装） |
| docx | 🅰️ Anthropic 官方 | 安全审计报告撰写 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 安全策略文档协作 |
| the-fool | 📦 jeffallan/claude-skills | 威胁建模的多角度分析 |

---

### A9. DevOps / SRE

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合 DevOps |
|-------|------|-----------------|
| jenkins-deploy | 📦 abcfed/claude-marketplace | Jenkins 测试环境发布管理 |
| terraform-module-library | 📦 wshobson/agents | Terraform IaC 模块库（5.1K 安装） |
| docker | 📦 bobmatnyc/claude-mpm-skills | Docker 最佳实践（456 安装） |
| ci-cd-best-practices | 📦 mindrally/skills | CI/CD 最佳实践（341 安装） |
| container-orchestration | 📦 0xdarkmatter/claude-mods | 容器编排（66 安装） |

---

### A10. 嵌入式工程师（Embedded Engineer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合嵌入式 |
|-------|------|----------------|
| embedded-systems | 📦 404kidwiz/claude-supercode-skills | 嵌入式系统开发指南（125 安装） |
| rust-pro | 📦 sickn33/antigravity-awesome-skills | Rust 系统编程（187 安装） |
| firmware-analyst | 📦 sickn33/antigravity-awesome-skills | 固件分析（118 安装） |
| doc-coauthoring | 🅰️ Anthropic 官方 | 硬件接口文档协作 |

---

### A11. 游戏开发者（Game Developer）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合游戏开发 |
|-------|------|-----------------|
| game-developer | 📦 jeffallan/claude-skills | 游戏开发最佳实践（999 安装） |
| algorithmic-art | 🅰️ Anthropic 官方 | 算法艺术，生成式图形创作 |
| performance-profiling | 📦 sickn33/antigravity-awesome-skills | 游戏性能优化（424 安装） |
| canvas-design | 🅰️ Anthropic 官方 | 视觉设计和艺术创作 |

---

### A12. 区块链/Web3 开发者（Blockchain/Web3 Dev）

> 继承：Level 0 + Level 1（工程通用）

| Skill | 来源 | 为什么适合 Web3 |
|-------|------|---------------|
| web3-testing | 📦 wshobson/agents | Web3 测试框架（3.3K 安装） |
| solidity-security-audit | 📦 mariano-aguero/solidity-security-audit-skill | Solidity 安全审计（23 安装） |
| frontend-design | 🅰️ Anthropic 官方 | DApp 前端开发 |
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | Web3 社区动态追踪 |
| x-research | 📦 rohunvora/x-research-skill | Crypto/Web3 社区讨论搜索 |

---

## B. 架构与技术管理类

### Level 1：技术管理通用

| Skill | 来源 | 为什么技术管理都需要 |
|-------|------|-------------------|
| planner | 📦 am-will/codex-skills | 技术方案设计和任务拆解 |
| the-fool | 📦 jeffallan/claude-skills | 重大技术决策的对抗性分析 |
| weekly-report | 📦 claude-office-skills/skills | 团队周报自动汇总 |
| meeting-minutes | 📦 github/awesome-copilot | 会议纪要自动生成 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 技术文档协作 |
| internal-comms | 🅰️ Anthropic 官方 | 内部沟通模板 |
| pptx | 🅰️ Anthropic 官方 | 演示文稿制作 |

---

### B1. 架构师（Software Architect）

> 继承：Level 0 + B 管理通用 + A Level 1（工程通用）

| Skill | 来源 | 为什么适合架构师 |
|-------|------|----------------|
| microservices-architect | 📦 jeffallan/claude-skills | 微服务架构设计（977 安装） |
| standup-meeting | 📦 supercent-io/skills-template | 架构评审和站会记录（10.5K 安装） |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 架构演示 PPT（1.3K 安装） |

---

### B2. 技术主管 / CTO（Tech Lead / CTO）

> 继承：Level 0 + B 管理通用 + B1（架构师）

| Skill | 来源 | 为什么适合 CTO |
|-------|------|-------------|
| news-summary | 📦 sundial-org/awesome-openclaw-skills | AI/技术趋势追踪 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 技术品牌和行业影响力 |
| x-research | 📦 rohunvora/x-research-skill | 技术社区动态搜索 |

---

### B3. 工程经理（Engineering Manager）

> 继承：Level 0 + B 管理通用

| Skill | 来源 | 为什么适合工程经理 |
|-------|------|------------------|
| standup-meeting | 📦 supercent-io/skills-template | 站会笔记自动化（10.5K 安装） |
| sprint-planner | 📦 eddiebe147/claude-settings | Sprint 规划（47 安装） |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 管理汇报 PPT（1.3K 安装） |
| xlsx | 🅰️ Anthropic 官方 | 团队数据分析（工时、velocity 等） |

---

## C. 产品类

### C1. 产品经理（Product Manager）

> 继承：Level 0

| Skill | 来源 | 为什么适合产品经理 |
|-------|------|------------------|
| planner | 📦 am-will/codex-skills | 需求拆解和实施方案 |
| doc-coauthoring | 🅰️ Anthropic 官方 | PRD 和技术文档协作 |
| meeting-minutes | 📦 github/awesome-copilot | 会议纪要自动生成 |
| the-fool | 📦 jeffallan/claude-skills | 产品决策的批判性分析 |
| pptx | 🅰️ Anthropic 官方 | 产品演示文稿 |
| xlsx | 🅰️ Anthropic 官方 | 数据分析和优先级矩阵 |
| product-manager | 📦 aj-geddes/claude-code-bmad-skills | 产品经理工作流（115 安装） |
| last30days | 📦 trailofbits/skills-curated | 用户反馈和竞品分析 |

---

### C2. 项目经理（Project Manager）

> 继承：Level 0

| Skill | 来源 | 为什么适合项目经理 |
|-------|------|------------------|
| planner | 📦 am-will/codex-skills | 项目计划和里程碑 |
| weekly-report | 📦 claude-office-skills/skills | 周报自动汇总 |
| meeting-minutes | 📦 github/awesome-copilot | 会议纪要 |
| standup-meeting | 📦 supercent-io/skills-template | 站会笔记（10.5K 安装） |
| sprint-planner | 📦 eddiebe147/claude-settings | Sprint 规划（47 安装） |
| the-fool | 📦 jeffallan/claude-skills | 风险评估和决策分析 |
| pptx | 🅰️ Anthropic 官方 | 项目汇报 |
| docx | 🅰️ Anthropic 官方 | 项目文档 |

---

## D. 设计类

### D1. UX/产品设计师（UX / Product Designer）

> 继承：Level 0

| Skill | 来源 | 为什么适合 UX 设计 |
|-------|------|------------------|
| frontend-design | 🅰️ Anthropic 官方 | 高质量 UI 原型生成 |
| webapp-testing | 🅰️ Anthropic 官方 | 可用性测试验证 |
| theme-factory | 🅰️ Anthropic 官方 | 设计系统和主题管理 |
| ui-design-review | 📦 mastepanoski/claude-skills | UI 设计审查（266 安装） |
| figma-design | 📦 manutej/luxor-claude-marketplace | Figma 设计协作（103 安装） |
| accessibility | 📦 addyosmani/web-quality-skills | 无障碍设计审计（3.9K 安装） |
| doc-coauthoring | 🅰️ Anthropic 官方 | 用户研究报告协作 |

---

### D2. UI/视觉设计师（UI / Visual Designer）

> 继承：Level 0

| Skill | 来源 | 为什么适合 UI/视觉 |
|-------|------|------------------|
| canvas-design | 🅰️ Anthropic 官方 | 视觉艺术创作 |
| theme-factory | 🅰️ Anthropic 官方 | 主题和品牌视觉系统 |
| frontend-design | 🅰️ Anthropic 官方 | 设计转前端代码 |
| algorithmic-art | 🅰️ Anthropic 官方 | 生成式算法艺术 |
| ui-design-review | 📦 mastepanoski/claude-skills | UI 设计审查（266 安装） |
| slack-gif-creator | 🅰️ Anthropic 官方 | 动效 GIF 创作 |

---

## E. 数据类

### E1. 数据分析师（Data Analyst）

> 继承：Level 0

| Skill | 来源 | 为什么适合数据分析 |
|-------|------|------------------|
| xlsx | 🅰️ Anthropic 官方 | Excel 数据处理和公式 |
| pdf | 🅰️ Anthropic 官方 | PDF 数据提取 |
| planner | 📦 am-will/codex-skills | 分析方案设计 |
| pptx | 🅰️ Anthropic 官方 | 分析结果演示 |
| data-visualization | 📦 smithery.ai | 数据可视化（55 安装） |
| recharts-patterns | 📦 yonatangross/orchestkit | 图表组件模式（82 安装） |

---

### E2. 数据科学家（Data Scientist）

> 继承：Level 0 + E1（数据分析师）

| Skill | 来源 | 为什么适合数据科学 |
|-------|------|------------------|
| ml-model-training | 📦 aj-geddes/useful-ai-prompts | ML 模型训练指南（135 安装） |
| ai-ml-data-science | 📦 vasilyu1983/ai-agents-public | AI/ML 全栈指南（120 安装） |
| systematic-debugging | 📦 obra/superpowers | 模型调试和数据管道排查 |
| tdd:test-driven-development | 📦 neolabhq/context-engineering-kit | 数据管道测试 |
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 论文和讲座总结 |
| news-summary | 📦 sundial-org/awesome-openclaw-skills | AI/ML 资讯追踪 |

---

## F. 内容与创作类

### F1. 技术写作（Technical Writer）

> 继承：Level 0

| Skill | 来源 | 为什么适合技术写作 |
|-------|------|------------------|
| api-documentation-generator | 📦 sickn33/antigravity-awesome-skills | 自动生成 API 文档 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 长文档协作和迭代 |
| docx | 🅰️ Anthropic 官方 | 专业文档格式处理 |
| changelog-maintenance | 📦 supercent-io/skills-template | CHANGELOG 维护（10.9K 安装） |
| readme-updater | 📦 ovachiever/droid-tings | README 自动更新（57 安装） |

---

### F2. 内容创作者（Content Creator）

> 继承：Level 0

| Skill | 来源 | 为什么适合内容创作 |
|-------|------|------------------|
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 播客/视频逐字稿总结 |
| baoyu-youtube-transcript | 📦 jimliu/baoyu-skills | 下载视频/音频，提取逐字稿 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 长文协作 |
| i18n-localization | 📦 sickn33/antigravity-awesome-skills | 中译英 Reddit 风格 |
| news-summary | 📦 sundial-org/awesome-openclaw-skills | AI 资讯日报 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 推特运营策略 |
| content-creation | 📦 anthropics/knowledge-work-plugins | Anthropic 内容创作指南（877 安装） |

---

### F3. 文案（Copywriter）

> 继承：Level 0

| Skill | 来源 | 为什么适合文案 |
|-------|------|-------------|
| doc-coauthoring | 🅰️ Anthropic 官方 | 文案协作和迭代 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 社交媒体文案策略 |
| i18n-localization | 📦 sickn33/antigravity-awesome-skills | 出海翻译 |
| content-creation | 📦 anthropics/knowledge-work-plugins | 内容创作指南（877 安装） |
| email-marketing | 📦 claude-office-skills/skills | 邮件营销文案（250 安装） |

---

## G. 营销与增长类

### G1. 市场营销（Marketing Manager）

> 继承：Level 0

| Skill | 来源 | 为什么适合市场营销 |
|-------|------|------------------|
| the-fool | 📦 jeffallan/claude-skills | 营销策略的多角度分析 |
| last30days | 📦 trailofbits/skills-curated | 市场调研和用户反馈 |
| pptx | 🅰️ Anthropic 官方 | 营销演示 |
| internal-comms | 🅰️ Anthropic 官方 | 内部通讯和报告 |
| canvas-design | 🅰️ Anthropic 官方 | 营销海报和视觉设计 |
| email-marketing | 📦 claude-office-skills/skills | 邮件营销（250 安装） |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 高质量 PPT（1.3K 安装） |
| seo | 📦 addyosmani/web-quality-skills | SEO 策略（4.2K 安装） |

---

### G2. 增长 / Growth Hacker

> 继承：Level 0

| Skill | 来源 | 为什么适合增长 |
|-------|------|-------------|
| planner | 📦 am-will/codex-skills | 增长实验方案设计 |
| xlsx | 🅰️ Anthropic 官方 | 增长数据分析 |
| last30days | 📦 trailofbits/skills-curated | 用户反馈和社区洞察 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 社交媒体增长策略 |
| seo | 📦 addyosmani/web-quality-skills | SEO 优化（4.2K 安装） |
| seo-optimizer | 📦 davila7/claude-code-templates | SEO 优化器（530 安装） |
| doc-coauthoring | 🅰️ Anthropic 官方 | A/B 测试文档 |
| n8n-workflow-automation | 📦 aaaaqwq/claude-code-skills | 增长自动化工作流（43 安装） |

---

### G3. SEO 专家（SEO Specialist）

> 继承：Level 0

| Skill | 来源 | 为什么适合 SEO |
|-------|------|-------------|
| seo | 📦 addyosmani/web-quality-skills | Google 工程师出品的 SEO 审计（4.2K 安装） |
| seo-optimizer | 📦 davila7/claude-code-templates | SEO 优化器（530 安装） |
| accessibility | 📦 addyosmani/web-quality-skills | 无障碍合规影响 SEO（3.9K 安装） |
| xlsx | 🅰️ Anthropic 官方 | 关键词和排名数据分析 |
| doc-coauthoring | 🅰️ Anthropic 官方 | SEO 内容优化 |
| last30days | 📦 trailofbits/skills-curated | 竞品关键词和用户意图分析 |
| brave-search | 📦 steipete/agent-scripts | 隐私友好的搜索替代，关键词调研（685 安装） |

---

### G4. 社交媒体运营（Social Media Manager）

> 继承：Level 0

| Skill | 来源 | 为什么适合社媒运营 |
|-------|------|------------------|
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 推特运营完整方法论 |
| x-research | 📦 rohunvora/x-research-skill | X/Twitter 内容搜索和趋势 |
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | Reddit 社区浏览和分析 |
| last30days | 📦 trailofbits/skills-curated | Reddit 讨论深度分析 |
| canvas-design | 🅰️ Anthropic 官方 | 社媒视觉内容设计 |

---

### G5. 社区运营（Community Manager）

> 继承：Level 0

| Skill | 来源 | 为什么适合社区运营 |
|-------|------|------------------|
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | Reddit 社区浏览 |
| last30days | 📦 trailofbits/skills-curated | 社区讨论分析 |
| x-research | 📦 rohunvora/x-research-skill | X/Twitter 社区动态 |
| weekly-report | 📦 claude-office-skills/skills | 社区周报 |
| community-builder | 📦 ncklrs/startup-os-skills | 社区建设指南（46 安装） |
| developer-advocacy | 📦 jonathimer/devmarketing-skills | 开发者关系（15 安装） |

---

## H. 商业与管理类

### H1. CEO / 创始人（Founder / CEO）

> 继承：Level 0

| Skill | 来源 | 为什么适合 CEO |
|-------|------|-------------|
| the-fool | 📦 jeffallan/claude-skills | 重大决策的对抗性分析 |
| planner | 📦 am-will/codex-skills | 战略规划拆解 |
| weekly-report | 📦 claude-office-skills/skills | 团队周报汇总 |
| meeting-minutes | 📦 github/awesome-copilot | 会议纪要 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 个人品牌和推特运营 |
| internal-comms | 🅰️ Anthropic 官方 | 内部沟通模板 |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 投资人/董事会 PPT（1.3K 安装） |
| news-summary | 📦 sundial-org/awesome-openclaw-skills | 行业趋势追踪 |
| last30days | 📦 trailofbits/skills-curated | 市场洞察 |
| alphaear-stock | 📦 rkiding/awesome-finance-skills | 股票和市场数据分析（284 安装） |

---

### H2. 独立开发者（Indie Hacker）

> 继承：Level 0 + A3（全栈工程师）全部

**最全面的角色**——身兼产品、开发、营销、运营。

| Skill | 来源 | 为什么适合独立开发者 |
|-------|------|-------------------|
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 推特运营核心——独立开发者获客主渠道 |
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | Reddit 推广和用户反馈 |
| i18n-localization | 📦 sickn33/antigravity-awesome-skills | 出海内容翻译 |
| frontend-design | 🅰️ Anthropic 官方 | 落地页和产品 UI |
| seo | 📦 addyosmani/web-quality-skills | 产品 SEO（4.2K 安装） |
| product-manager | 📦 aj-geddes/claude-code-bmad-skills | 一人当 PM（115 安装） |
| stripe-payments | 📦 claude-office-skills/skills | 支付集成——独立开发者 SaaS 刚需（219 安装） |

---

### H3. 咨询师 / 顾问（Consultant）

> 继承：Level 0

| Skill | 来源 | 为什么适合咨询 |
|-------|------|-------------|
| the-fool | 📦 jeffallan/claude-skills | 咨询分析的多角度框架 |
| planner | 📦 am-will/codex-skills | 咨询方案设计 |
| docx | 🅰️ Anthropic 官方 | 咨询报告 |
| pptx | 🅰️ Anthropic 官方 | 咨询演示 |
| xlsx | 🅰️ Anthropic 官方 | 数据分析 |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 高端 PPT（1.3K 安装） |
| last30days | 📦 trailofbits/skills-curated | 行业调研 |
| email-marketing | 📦 claude-office-skills/skills | 客户沟通邮件（250 安装） |

---

### H4. 销售（Sales）

> 继承：Level 0

| Skill | 来源 | 为什么适合销售 |
|-------|------|-------------|
| pptx | 🅰️ Anthropic 官方 | 客户提案 |
| docx | 🅰️ Anthropic 官方 | 商务文档 |
| xlsx | 🅰️ Anthropic 官方 | 销售数据和管道分析 |
| internal-comms | 🅰️ Anthropic 官方 | 内部汇报 |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 高质量提案 PPT（1.3K 安装） |
| email-marketing | 📦 claude-office-skills/skills | 客户邮件（250 安装） |
| x-research | 📦 rohunvora/x-research-skill | 客户洞察搜索 |

---

## K. 支持职能类（Support Functions）

### K1. HR / 招聘（HR / Recruiter）

> 继承：Level 0

| Skill | 来源 | 为什么适合 HR |
|-------|------|-------------|
| doc-coauthoring | 🅰️ Anthropic 官方 | JD 撰写、面试题设计、入职手册 |
| xlsx | 🅰️ Anthropic 官方 | 招聘数据分析、人才漏斗 |
| pptx | 🅰️ Anthropic 官方 | 组织汇报、招聘报告 |
| internal-comms | 🅰️ Anthropic 官方 | 内部公告、组织变更通知 |
| meeting-minutes | 📦 github/awesome-copilot | 面试记录、团队会议纪要 |
| the-fool | 📦 jeffallan/claude-skills | 组织决策的多角度分析 |
| x-research | 📦 rohunvora/x-research-skill | 人才市场趋势搜索 |
| email-marketing | 📦 claude-office-skills/skills | 招聘邮件和候选人沟通（250 安装） |

---

### K2. 法务 / 合规（Legal / Compliance）

> 继承：Level 0

| Skill | 来源 | 为什么适合法务 |
|-------|------|-------------|
| docx | 🅰️ Anthropic 官方 | 合同、法律文书撰写 |
| pdf | 🅰️ Anthropic 官方 | 法规文档提取和分析 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 政策文档协作 |
| the-fool | 📦 jeffallan/claude-skills | 合规风险的多角度分析 |
| xlsx | 🅰️ Anthropic 官方 | 合规审计数据整理 |
| planner | 📦 am-will/codex-skills | 合规方案设计 |

---

### K3. 财务 / 会计（Finance / Accounting）

> 继承：Level 0

| Skill | 来源 | 为什么适合财务 |
|-------|------|-------------|
| xlsx | 🅰️ Anthropic 官方 | 财务报表、预算管理、数据分析 |
| pdf | 🅰️ Anthropic 官方 | 发票、合同等 PDF 处理 |
| docx | 🅰️ Anthropic 官方 | 财务报告 |
| pptx | 🅰️ Anthropic 官方 | 财务汇报演示 |
| the-fool | 📦 jeffallan/claude-skills | 投资决策分析 |
| planner | 📦 am-will/codex-skills | 预算规划 |
| alphaear-stock | 📦 rkiding/awesome-finance-skills | 股票和财务数据分析（284 安装） |

---

### K4. 客服 / 客户支持（Customer Support）

> 继承：Level 0

| Skill | 来源 | 为什么适合客服 |
|-------|------|-------------|
| doc-coauthoring | 🅰️ Anthropic 官方 | FAQ、帮助文档编写 |
| internal-comms | 🅰️ Anthropic 官方 | 客户沟通模板 |
| xlsx | 🅰️ Anthropic 官方 | 工单数据分析、满意度统计 |
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | 社区用户反馈监控 |
| last30days | 📦 trailofbits/skills-curated | 用户问题趋势分析 |

---

## I. 学术与教育类

### I1. 研究员（Researcher）

> 继承：Level 0

| Skill | 来源 | 为什么适合研究 |
|-------|------|-------------|
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 论文/讲座/播客总结 |
| mentoring-juniors | 📦 github/awesome-copilot | 引导式学习新领域 |
| the-fool | 📦 jeffallan/claude-skills | 研究方法论批判 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 论文协作 |
| xlsx | 🅰️ Anthropic 官方 | 研究数据分析 |
| news-summary | 📦 sundial-org/awesome-openclaw-skills | 领域资讯追踪 |
| brave-search | 📦 steipete/agent-scripts | 隐私友好的学术搜索（685 安装） |
| notion-mcp | 📦 dokhacgiakhoa/antigravity-ide | 研究笔记和知识库管理 |
| baoyu-youtube-transcript | 📦 jimliu/baoyu-skills | 学术讲座/会议视频下载 |

---

### I2. 教师 / 讲师（Educator）

> 继承：Level 0

| Skill | 来源 | 为什么适合教育 |
|-------|------|-------------|
| mentoring-juniors | 📦 github/awesome-copilot | 引导式教学设计 |
| pptx | 🅰️ Anthropic 官方 | 教学课件 |
| docx | 🅰️ Anthropic 官方 | 教学材料和试卷 |
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 教学视频总结 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 课程设计协作 |
| elite-powerpoint-designer | 📦 willem4130/claude-code-skills | 高质量教学课件（1.3K 安装） |

---

### I3. 学生（Student）

> 继承：Level 0

| Skill | 来源 | 为什么适合学生 |
|-------|------|-------------|
| mentoring-juniors | 📦 github/awesome-copilot | 引导式学习新技术 |
| systematic-debugging | 📦 obra/superpowers | 学习调试方法论 |
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 课程/讲座笔记 |
| doc-coauthoring | 🅰️ Anthropic 官方 | 论文/报告写作 |
| tdd:test-driven-development | 📦 neolabhq/context-engineering-kit | 通过测试学编程 |
| baoyu-youtube-transcript | 📦 jimliu/baoyu-skills | 下载学习视频，提取字幕 |

---

## J. 复合 / 自由职业类

### J1. 自由职业者（Freelancer）

> 继承：Level 0 + 技术 Skill 取决于专业领域

| Skill | 来源 | 为什么适合自由职业 |
|-------|------|------------------|
| planner | 📦 am-will/codex-skills | 项目方案和报价 |
| weekly-report | 📦 claude-office-skills/skills | 客户周报 |
| docx | 🅰️ Anthropic 官方 | 合同/提案文档 |
| xlsx | 🅰️ Anthropic 官方 | 发票/财务管理 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 个人品牌建设 |
| internal-comms | 🅰️ Anthropic 官方 | 客户沟通模板 |
| frontend-design | 🅰️ Anthropic 官方 | 作品集/个人站 |
| trello | 📦 membranedev/application-skills | 项目看板管理（36 安装） |
| stripe-payments | 📦 claude-office-skills/skills | 支付集成（219 安装） |
| n8n-workflow-automation | 📦 aaaaqwq/claude-code-skills | 自动化工作流（43 安装） |

---

### J2. 技术布道师（Developer Advocate）

> 继承：Level 0 + A Level 1（工程通用）

| Skill | 来源 | 为什么适合技术布道 |
|-------|------|------------------|
| doc-coauthoring | 🅰️ Anthropic 官方 | 技术博客和教程 |
| pptx | 🅰️ Anthropic 官方 | 技术演讲 |
| podcast-to-content-suite | 📦 onewave-ai/claude-skills | 会议/播客内容总结 |
| baoyu-youtube-transcript | 📦 jimliu/baoyu-skills | 技术视频素材下载 |
| x-twitter-growth | 📦 alirezarezvani/claude-skills | 技术内容社交传播 |
| x-research | 📦 rohunvora/x-research-skill | 技术社区动态 |
| research-by-reddit | 📦 muzhicaomingwang/ai-ideas | 社区互动 |
| developer-advocacy | 📦 jonathimer/devmarketing-skills | DevRel 工作指南（15 安装） |

---

## 附录：外部 Skill 仓库推荐

以下仓库包含大量按角色组织的高质量 Skill，可按需引入：

| 仓库 | Stars | Skill 数 | 特色 |
|------|-------|---------|------|
| alirezarezvani/claude-skills | 6,267 | 205 | **按角色分类最全**：工程(56)、营销(43)、C-Level(28)、产品(14)、法规合规(12)、项目管理(6) |
| anthropics/skills | 99,617 | 16 | **Anthropic 官方**：Creative、Development、Enterprise、Document |
| VoltAgent/awesome-agent-skills | 12,292 | 500+ | **官方团队发布**：含 Anthropic/Vercel/Stripe/Cloudflare 等 |
| addyosmani/web-quality-skills | 4,200+ | 2 | **Google 工程师出品**：SEO + Accessibility |

**安装方式**：`npx skills add <owner/repo@skill-name>`

**特别说明**：`alirezarezvani/claude-skills` 仓库中的以下子集对特定角色特别有价值：
- **营销角色**：marketing-skill/ 下 43 个 Skill 覆盖 SEO、CRO、内容、渠道、增长、情报、销售 7 个 Pod
- **C-Level 角色**：c-level-advisor/ 下 28 个 Skill 覆盖 CEO/CTO/CFO/CMO/COO/CPO/CRO/CHRO/CISO 9 个 C-Suite 角色
- **法规合规**：ra-qm-team/ 下 12 个 Skill 覆盖 GDPR、ISO 13485、FDA、MDR 等
- **产品角色**：product-team/ 下 14 个 Skill 包含竞品拆解、实验设计、路线图沟通等

---

## 维护说明

### 更新流程

1. **新增 Skill**：搜索 `npx skills find` → 评估质量 → 添加到对应角色
2. **Skill 废弃**：及时移除或标注替代品
3. **新增角色**：在对应大类末尾添加新 section，更新继承关系
4. **外部 Skill 更新**：定期 `npx skills check` 检查更新

### 质量标准

- 外部 Skill 推荐标准：安装量 > 20 或内容质量经过人工验证
- 每个角色保持 5-10 个专属推荐（不含继承）
- 同一能力不推荐多个 Skill，选最优的一个

### 统计

| 指标 | 数量 |
|------|------|
| 角色大类 | 11 |
| 具体角色 | 42 |
| 内置 Skill | 0 |
| 官方 Skill | 16 |
| 外部 Skill（精选） | 30+ |
| 外部 Skill（附录仓库可引入） | 200+ |
| 覆盖率 | 100%（每个角色至少 5 条推荐） |
| 数据来源 | skills.sh（89,592 总量）、GitHub（6 个 awesome-list）、X/Reddit |
| 角色参考 | agency-agents（110+ 角色，msitarzewski/agency-agents） |
