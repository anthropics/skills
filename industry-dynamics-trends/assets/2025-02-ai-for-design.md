# AI for Design 行业前沿洞察（2025年2月）月刊

> 🤖 AI 初稿：基于公开信源检索与核查

**本月动态总览**：
2 月在**产品应用侧**：Framer 上线 Scale 工具与性能优化、Visily 发布 Auto-Prototyping 自动连线原型、Adobe Firefly 视频模型 beta 与多模态创作流程落地；Figma 与 OpenAI Codex 打通设计—代码双向工作流（MCP、get_design_context、运行界面回写 Figma）；Designs.ai 推出 AI Design 提示驱动视觉生成与品牌一致模板——设计工具链的「键盘可控迭代」「从线框到可交互原型」以及「画布与代码双向同步」的自动化程度明显提升。**模型/技术侧**：Firefly Video 支持 1080p 商用级输出与 Image-to-Video 工作流；学术方向出现将 Prompt 具象为可操作界面对象的研究（AI-Instruments）、以及面向文生图产品设计的维度脚手架（DesignWeaver）。**行业关注**：字节跳动 Seedance 2.0 公布（官方日期 2026 年 2 月 12 日，待确认），多模态音视频联合生成与「导演级」可控性成为 AI 视频赛道重点；Fortune 等指出 OpenAI 持续强化产品设计侧投入。本月最值得关注的效能突破点：**设计—代码双向工作流**（Figma + Codex）、**原型自动化**（Visily）、**视频/动效生成生产可用**（Adobe），以及**设计系统与 AI 协作**的实操方法论（UXmatters）。

---

### 动态 1：Framer 上线 Scale 工具，支持按倍数/目标尺寸缩放并保留样式
* **【最新动态】**：Framer 于 2025 年 2 月 25 日发布 February Update，新增 Scale Tool（快捷键 `K`）：可按倍数或目标尺寸缩放图层，并保持圆角、描边、字号等样式一致；支持键盘输入数值（如 `2`、`0.5`）后回车快速迭代；同期 locale 重定向速度提升约 100%，Video/Slideshow/Search 组件的 INP 与懒加载得到优化。[1](#ref-1)
* **【行业风向】**：企业级设计交付中「响应式与多尺寸产出」的迭代成本降低，产研在 Framer 内即可用同一套资产快速验证不同断点与比例，有利于设计系统与前端协作的标准化。
* **【设计启发点】**：Leader 可将 Scale 纳入设计规范与培训（统一用 `K` 做多尺寸校验）；一线设计师在 Framer 中做 landing 或组件库时，优先用 Scale 做倍数缩放再微调，减少重复劳动。
* **【配图/视频】**：![Framer Scale 工具示意](https://framerusercontent.com/images/UGv0R5sC2zXM4KIJNpPD0EsbJ0.png?width=1600&height=900) [11](#ref-11)

### 动态 2：Adobe Firefly Video Model 进入 beta，多模态创作与 1080p 商用输出
* **【最新动态】**：Adobe 于 2025 年 2 月 12 日在 Firefly 网页应用中推出 Firefly Video Model（beta），支持文生视频、图生视频、风格与机位控制；输出为 1080p，官方定位为「production-ready」；与 Photoshop web、Premiere Pro 打通，并新增 Firefly Standard/Pro 档位及即将推出的 Firefly Premium。[2](#ref-2)
* **【行业风向】**：品牌与视频团队可在「IP 友好、商用安全」前提下用 AI 生成 B-roll、动效与概念视频，缩短从创意到成片的周期；设计团队在动效与叙事类交付中多了一条可合规使用的工具链。
* **【设计启发点】**：Leader 可评估 Firefly 视频能力用于品牌视频、动效与故事板产出的 ROI；一线设计师可将 Firefly 用于快速生成背景与氛围素材，再在 PS/Premiere 中精修，注意人物等敏感内容仍建议人工校验（官方称该部分持续优化中）。
* **【配图/视频】**：![Firefly Video 界面示意](https://blog.adobe.com/en/publish/2025/02/12/media_19846d436079bbe9de6505cc71ae92758436e7468.png?width=1200&format=pjpg&optimize=medium) [12](#ref-12)；博客内另含多段 Firefly 视频演示（文生视频、图生视频、2D/3D 动效等），见来源 [2](#ref-2)。

### 动态 3：UXmatters 发文探讨设计系统与 AI 协作，含 Figma 数据可视化组件案例
* **【最新动态】**：UXmatters 于 2025 年 2 月 3 日发布《Smarter, Faster, Human: The Future of Design Systems with AI》，以企业设计系统与 AI 协作为主线，给出可访问色板扩展、Figma 数据可视化组件的实操案例；文中引用「AI 生成 WCAG 合规色板使调色时间减少 80% 以上」及「六类数据可视化组件从数月压缩至约三周」等结果。[3](#ref-3)
* **【行业风向】**：设计系统从静态规范向「AI 辅助生成与校验 + 人工决策」的协作模式演进，企业级可访问性（WCAG）与组件文档的自动化成为可量化提效点。
* **【设计启发点】**：Leader 可推动在设计系统中引入「AI 生成初稿 + 人工校验」流程，并明确可访问性为必检项；一线设计师可复用文中 Prompt 思路（如为图表生成可配置属性与文档），提升组件库与文档的迭代速度。
* **【配图/视频】**：配图与案例截图见来源页 [3](#ref-3)。

### 动态 4：Visily 发布 Auto-Prototyping，AI 自动连接页面与元素生成可交互原型
* **【最新动态】**：Visily 于 2025 年 2 月 24 日发布 Auto-Prototyping 功能：基于对 UX 流程的理解，自动识别页面与元素间的连接关系并生成交互原型，将线框到可点击原型的步骤压缩到秒级；当前为第一版，计划后续支持更复杂流程与更精确连线。[4](#ref-4)
* **【行业风向】**：原型制作从「逐屏手动连线」转向「AI 推断 + 人工修正」，产品与设计在早期验证阶段的交付速度提升，对需求澄清与评审节奏有直接影响。
* **【设计启发点】**：Leader 可将 Visily 纳入「快速验证与演示」工具栈，与现有 Figma/Framer 流程配合；一线设计师在线框阶段保持清晰的命名与层级，便于 Auto-Prototyping 更准确推断跳转关系。
* **【配图/视频】**：![Visily Auto-Prototyping 示意](https://www.visily.ai/wp-content/uploads/2025/02/Auto-prototype-1024x731.jpg) [13](#ref-13)（线框自动连线为可交互原型；来源页含演示视频 [4](#ref-4)）。

### 动态 5：AI-Instruments 研究将 Prompt 具象为可操作界面对象，支持非线式设计探索
* **【最新动态】**：arXiv 于 2025 年 2 月收录论文《AI-Instruments: Embodying Prompts as Instruments…》（编号 2502.18736），提出将「提示」具象为可直接操作的界面对象（instruments），用户可非线式探索多种解释、反思并切换方向，而非仅依赖线性对话；面向图像生成等创意 AI 辅助设计场景。[5](#ref-5)
* **【行业风向】**：若被工具产品采纳，设计工具中的「与 AI 协作」形态可能从纯聊天框扩展为可拖拽、可复用的控件，更贴近设计师的思维与工作流。
* **【设计启发点】**：Leader 可关注后续是否有设计工具引入「Prompt 即控件」类交互；一线设计师在评估新 AI 功能时，可思考「是否支持多方案并排、撤销与分支」以提升可控性。
* **【配图/视频】**：论文摘要页含界面与工作流示意图，见来源 [5](#ref-5)。

### 动态 6：字节跳动 Seedance 2.0 正式发布，多模态音视频联合生成与导演级可控（官方公布日期：2026年2月12日）
* **【最新动态】**：字节跳动 Seed 团队公布 Seedance 2.0 于 **2026 年 2 月 12 日**正式发布。采用统一多模态音视频联合生成架构，支持文字、图片、音频、视频混合输入（最多 9 张图、3 段视频、3 段音频 + 自然语言指令）；支持 15 秒高质量多镜头输出、双声道音频、视频延长与定向编辑；在复杂运动与多主体交互场景下的可用率与物理准确度显著提升；计划接入即梦 AI、豆包、火山方舟等平台。[6](#ref-6)
* **【行业风向】**：AI 视频从「单段生成」走向「导演级」可控与长叙事，影视、广告、电商、游戏等内容制作成本与周期有望进一步压缩；与 Adobe Firefly、Sora、Runway 等形成差异化（多模态参考 + 编辑/延长）。
* **【设计启发点】**：Leader 可将 Seedance 2.0 纳入视频/动效工具选型与前瞻跟踪；一线设计师在品牌视频、故事板、B-roll 需求中可关注即梦/豆包端后续 2.0 能力，人物主体参考须取得授权（官方说明已强调）。
* **【配图/视频】**：配图与能力演示见来源页 [6](#ref-6)。

### 动态 7：DesignWeaver 研究为文生图产品设计提供维度脚手架，提升新手 Prompt 质量
* **【最新动态】**：arXiv 于 2025 年 2 月收录论文《DesignWeaver: Dimensional Scaffolding for Text-to-Image Product Design》（编号 2502.09867），通过结构化维度脚手架帮助新手为文生图模型撰写提示，突出产品设计关键维度；在 52 名新手用户实验中，参与者能生成更长、更领域相关的 Prompt，产出更多样、更具创意的产品设计。[7](#ref-7)
* **【行业风向】**：设计工具与 AI 的衔接从「自由文本 Prompt」向「结构化维度 + 自由发挥」演进，有利于降低入门门槛并提升企业内非设计师角色的产出质量。
* **【设计启发点】**：Leader 可在内部 Prompt 规范或培训中引入「维度脚手架」思路（如材质、场景、风格、比例等）；一线设计师在带业务方用文生图时可先框定维度再细化文案，减少无效生成。
* **【配图/视频】**：论文摘要页含维度脚手架与实验示意图，见来源 [7](#ref-7)。

### 动态 8：Fortune 解读 OpenAI 强化产品设计投入对 AI 未来的影响
* **【最新动态】**：Fortune 于 2025 年 2 月 13 日发文《What OpenAI's growing focus on product design tells us about AI's future》，指出 OpenAI 自 ChatGPT 以来持续强化产品设计与用户体验，将简单可用的对话界面作为差异化能力；并讨论在开源与竞品压力下，产品设计对 AI 普及与商业化的关键作用。[8](#ref-8)
* **【行业风向】**：大模型能力趋同背景下，面向设计/体验的投入成为厂商战略重点，设计团队在 AI 产品定义与交互规范上的话语权有望提升。
* **【设计启发点】**：Leader 可从「AI 产品设计」视角参与公司 AI 路线图讨论；一线设计师可关注 ChatGPT、Copilot 等产品的交互迭代，提炼可复用的模式用于内部工具或客户产品。
* **【配图/视频】**：配图见来源页 [8](#ref-8)。

### 动态 9：Figma 与 Codex 打通设计—代码双向工作流，MCP 支持设计上下文入代码与运行界面回写 Figma
* **【最新动态】**：Figma 于 2025 年 2 月 26 日发布博客，宣布通过 Figma MCP server 与 OpenAI Codex 集成：开发者可在 Codex 中基于 Figma 选区链接获取 `get_design_context`（布局、样式、组件信息），用自然语言生成实现并保持与设计系统一致；支持将运行中的 UI 通过 `generate_figma_design` 回写为可编辑的 Figma 画布，实现「从代码到画布」的往返迭代。当前为 beta，需在 Codex 桌面应用中安装 Figma MCP server。[9](#ref-9)
* **【行业风向】**：设计—开发 handoff 从「交付静态稿 + 标注」向「设计上下文直连 LLM、代码与画布双向同步」演进，产研协作的中间损耗与重复劳动有望下降；企业设计系统与代码库的映射成为 AI 生成质量的关键输入。
* **【设计启发点】**：Leader 可评估在设计—开发流程中引入 MCP + Codex 的试点（明确设计文件命名、选区与组件规范）；一线设计师在交付时提供「复制选区链接」并保持组件/变量一致，便于开发侧 get_design_context 准确；开发侧可优先在原型或内部工具上试用「运行界面 → Figma」回写以验证流程。
* **【配图/视频】**：![Codex 与 Figma 工作流示意](https://cdn.sanity.io/images/599r6htc/regionalized/91a44fffb71747596e2fcc9f29fb28b374719dfb-1021x984.png?q=75&fit=max&auto=format) [14](#ref-14)（设计→代码→画布往返；更多步骤截图见来源 [9](#ref-9)）。

### 动态 10：Designs.ai 推出 AI Design，提示驱动生成品牌一致视觉与模板组合
* **【最新动态】**：Designs.ai 于 2025 年 2 月 26 日发布 AI Design 产品：通过文本提示与风格选择即时生成视觉，支持「克隆设计」在约 30 秒内生成变体、AI 驱动的智能定制建议、一键多尺寸/多平台导出；首发约 5,000 个 AI 模板，可组合生成大量设计变体。官方定位为面向营销、创业与代理的「提示驱动」替代方案（相对 Canva、Adobe 等模板式工具），已全球上线 designs.ai/ai-design。[10](#ref-10)
* **【行业风向】**：非设计师角色的品牌视觉产出门槛降低，设计团队需在「品牌规范 + AI 初稿」流程上明确校验节点与可交付标准，避免品牌一致性稀释。
* **【设计启发点】**：Leader 可评估将 AI Design 用于营销物料、社媒与演示的初稿生成，并规定品牌色、字体与版式的必检项；一线设计师可为业务方编写「维度化」提示规范（场景、风格、比例等），提升生成结果可用率。
* **【配图/视频】**：配图与产品界面见来源页 [10](#ref-10)。

---

### 总结与展望
2 月动态集中在**原型与动效的自动化**（Visily、Framer）、**多模态生成的生产可用化**（Adobe Firefly Video）、**设计—代码双向工作流**（Figma + Codex）、以及**设计系统与 AI 协作的方法论**（UXmatters）。建议企业设计管理：将「原型自动化」「视频/动效 AI」与「Figma MCP + Codex」纳入本年度工具与流程评估，明确合规与可访问性标准；在团队培训中增加「AI 初稿 + 人工校验」与键盘/快捷键工作流，以提升单兵与协作效能。展望 3 月，可继续跟踪 Figma 生态与 Adobe Creative Cloud 的 AI 功能落地节奏、Codex 与 Claude Code to Figma 等双向能力的落地案例，以及学术成果向产品形态的转化。

---

### 来源链接索引
- <a id="ref-1"></a>[1](#ref-1) February Update: Scale - Framer (2025年2月25日)：<a href="https://www.framer.com/updates/february-update-2025" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-2"></a>[2](#ref-2) Meet Firefly Video Model: AI-Powered creation with unparalleled creative control - Adobe Blog (2025年2月12日)：<a href="https://blog.adobe.com/en/publish/2025/02/12/meet-firefly-video-model-ai-powered-creation-with-unparalleled-creative-control" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-3"></a>[3](#ref-3) Smarter, Faster, Human: The Future of Design Systems with AI - UXmatters (2025年2月3日)：<a href="https://www.uxmatters.com/mt/archives/2025/02/smarter-faster-human-the-future-of-design-systems-with-ai.php" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-4"></a>[4](#ref-4) Introducing Auto-Prototyping: Smarter, Faster Prototyping - Visily Blog (2025年2月24日)：<a href="https://www.visily.ai/blog/announcing-auto-prototyping" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-5"></a>[5](#ref-5) AI-Instruments: Embodying Prompts as Instruments… - arXiv (2025年2月)：<a href="https://arxiv.org/abs/2502.18736" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-6"></a>[6](#ref-6) Seedance 2.0 正式发布 - ByteDance Seed (2026年2月12日；官方标注日期，待确认)：<a href="https://seed.bytedance.com/en/blog/seedance-2-0-%E6%AD%A3%E5%BC%8F%E5%8F%91%E5%B8%83" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-7"></a>[7](#ref-7) DesignWeaver: Dimensional Scaffolding for Text-to-Image Product Design - arXiv (2025年2月)：<a href="https://arxiv.org/abs/2502.09867" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-8"></a>[8](#ref-8) What OpenAI's growing focus on product design tells us about AI's future - Fortune (2025年2月13日)：<a href="https://fortune.com/2025/02/13/openai-ai-product-design-deepseek-open-source" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-9"></a>[9](#ref-9) Building frontend UIs with Codex and Figma - Figma Blog (2025年2月26日)：<a href="https://www.figma.com/blog/introducing-codex-to-figma/" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-10"></a>[10](#ref-10) Designs.ai Introduces AI Design - 新闻稿 (2025年2月26日)：<a href="https://lifestlyeweek.com/press-release/2025-02-26/16341/designs-ai-introduces-ai-design-revolutionizing-creativity-with-intelligent-automation" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-11"></a>[11](#ref-11) Framer February Update 配图 - 截图 - Framer (2025年2月25日)：<a href="https://www.framer.com/updates/february-update-2025" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-12"></a>[12](#ref-12) Firefly Video Model 配图 - 截图 - Adobe Blog (2025年2月12日)：<a href="https://blog.adobe.com/en/publish/2025/02/12/meet-firefly-video-model-ai-powered-creation-with-unparalleled-creative-control" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-13"></a>[13](#ref-13) Auto-Prototyping 配图 - 截图 - Visily Blog (2025年2月24日)：<a href="https://www.visily.ai/blog/announcing-auto-prototyping" target="_blank" rel="noopener noreferrer">打开</a>
- <a id="ref-14"></a>[14](#ref-14) Codex and Figma 工作流配图 - 截图 - Figma Blog (2025年2月26日)：<a href="https://www.figma.com/blog/introducing-codex-to-figma/" target="_blank" rel="noopener noreferrer">打开</a>
