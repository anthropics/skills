---
name: skill-smith
description: 想把经验做成 AI 技能？它照高口碑技能的套路帮你从零写一个：结构、触发词、避坑全包；写完机器体检（格式/死链/体积/双源），老技能也能升级。做技能的技能。触发词：写个skill、技能开发、skill体检、技能升级。
display_name: AI技能制造机（写/体检/升级技能包）
display_name_en: Skill Smith
description_zh: 写新技能、体检旧技能、升级迭代一条龙，按平台标准出可直接上传的包。
description_en: Create, audit and upgrade AI skills into platform-ready packages.
examples_zh:
- "帮我写一个新技能包"
- "体检这个技能有什么问题"
- "按平台标准升级我的技能"
examples_en:
- "Write me a new skill package"
- "Audit this skill for problems"
- "Upgrade my skill to the platform standard"
version: 1.2.2
author: "ayan"
---

# skill-smith · skill 工程台

定位一句话：给 Claude Code skill 做工程管理——从零锻造、体检安检、棘轮升级，八条模式是唯一标准源。

## 30秒速览

- 三模式：生成（九步出包）／安检（机检+九维评分）／升级（棘轮循环）。
- 评分满分100、交付线85（新包75）、机检有FAIL时语义分封顶59。
- 评分铁律：每个分数带证据（文件+行号或原文≤40字），空分无效；评分与编辑不同上下文。

## 模式路由

| 任务说法 | 模式 | 执行文件 |
|---|---|---|
| 写个skill／造skill／新建skill／skill模板 | 生成 | references/create-playbook.md 九步 |
| skill安检／体检／评分／质量／审计 | 安检 | scripts/skill-audit.js + references/audit-rubric.md |
| 优化skill／升级skill／重构／瘦身 | 升级 | references/upgrade-loop.md（先安检拿基线） |
| skill写作纪律／文档指针化／高危动作标注 | 参考 | references/writing-spec.md |
| 什么是好skill／八条模式 | 参考 | references/eight-patterns.md |

任何模式开工前先读 references/lessons-ledger.md（老坑不重踩）。

## 安检速记

机检：`node scripts/skill-audit.js <目录>`（frontmatter／死链／孤儿文件／双源／体积／脚本语法／模糊纪律词）→ FAIL 清零才做语义九维。
九维＝frontmatter10／路由化15／数字化15／关卡10／诚实15／机器可检15／失败资产5／交接协议5／预期管理10。分级出口与报告格式见 references/audit-rubric.md。

## 升级速记

单变量·字符变化≤10%·备份先行·子agent独立评分·新分>旧分才留·循环≤5轮·连续2轮Δ<0.5分停。硬规则、产物表、反例黑名单见 references/upgrade-loop.md。功能语义改动走 change-guard，不进循环。

## 纪律可触线表（本skill自守）

| 场景 | 上限 | 到顶后动作 |
|---|---|---|
| 生成模式追问 | 同一需求至多2轮 | 第3轮起用默认假设，产物顶部声明「基于假设X」 |
| 安检读取被检文件 | 单任务至多读5份，大文件只读标题结构+重点段 | 超出回索引表重新定位，禁整库通读 |
| 升级循环 | ≤5轮 | 触顶问用户：加1轮／弱项重写／收工 |
| 单轮编辑 | 字符变化≤10% | 超了拆成下一轮 |
| 棘轮无增益 | 连续2轮总分Δ<0.5 | 停止循环，收口出前后对比报告 |

长任务进度锚：多目录安检/多模块任务每完成一块给一行「✓ A完成（N条，M待验证），下一个B」，中断续跑不重扫。

## 诚实状态

- 评分必带证据；机检输出原样贴进报告，禁改写。
- 并行子代理/多轮扫描的报告=声称不是证据：入报告前复核行号、去重剔误报、计数对账。
- 被检skill缺文件/读不动 → 报告里明说缺什么，不猜。
- 语义评审拿不准的维度取低一级分并标[推断]。

## 预期管理

- 负面承诺：不替被检skill做功能决策；不在升级循环里动功能语义；不承诺评分高的skill内容创意就强。
- 效果承诺三件套：设计目标＝工程质量与头部对齐；不承诺＝创意水平；可验证指标＝九维前后分差＋机检FAIL数变化。

## 自检清单（证据制）

□ 本skill自身改动后 `node scripts/skill-audit.js <本目录>` exit 0 —— 贴汇总行
□ 出过的评分报告每维带证据 —— 抽2维贴证据原文
□ 新踩的坑已追加 references/lessons-ledger.md —— 贴条目号

## 参考文件索引

| 文件 | 一句话职责 |
|---|---|
| references/eight-patterns.md | 八条模式宪法（定义/判据/反例），一切评分锚点 |
| references/audit-rubric.md | 九维评分细则＋分级出口＋报告格式 |
| references/create-playbook.md | 生成九步（追问上限＋自检闭环） |
| references/upgrade-loop.md | 升级硬规则／流程／产物表／反例黑名单 |
| references/writing-spec.md | skill 写作纪律五原则＋标准结构＋Pitfalls（生成/升级共用） |
| references/lessons-ledger.md | 现场坑账本，开工先读 |
| scripts/skill-audit.js | 机器安检器（被检skill与本skill通用） |
| templates/skill-skeleton.md | 新skill骨架模板 |

## 免责声明

- 本 skill 按「现状」提供（MIT 许可），作者不对使用结果作任何保证。
- 使用者自负合规责任：请遵守你所在平台的服务条款与当地法规；生成的任何内容发布前请自查（广告法、违禁词、版权）。
- 本包不代任何第三方品牌、不含第三方私有数据；文中出现的第三方产品名仅为功能互操作说明或示例，与相应方无关联、无赞助。
