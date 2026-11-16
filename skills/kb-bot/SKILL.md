---
name: kb-bot
description: 装了就有一个越用越懂你的资料问答机器人：问它公司文档/产品资料，答案带来源和时间；没答过的现查，答完自动记进库，下次秒答；答案过期自动提醒复核，绝不编造。触发词：问库、查库、知识库问答、内部资料、现在多少。
display_name: 越问越懂你的知识库机器人
display_name_en: Knowledge Base Q&A Bot
description_zh: 把你的文档喂进去，回答带来源、坏答案自动防腐，越问越懂你（零库出厂自建）。
description_en: A Q&A bot over your own docs with sources and stale-answer checks.
examples_zh:
- "用我的文档搭一个问答机器人"
- "这个问题知识库里怎么说的"
- "把这批资料吸收进知识库"
examples_en:
- "Build a Q&A bot from my docs"
- "What does the KB say about this"
- "Ingest these files into the KB"
version: 1.0.3
author: "ayan"
---

# kb-bot：知识库问答 bot（懒吸收 + 防腐）

一句话：装了这个 skill，就有一个绑定的 kb-bot 驻岗子 agent 替你答库内领域的问题——库里有的直答，没有的现取并落库，答过的都变成可检索、带来源、带保鲜期的节点。

## 装 / 卸

装：
1. 整个 `kb-bot/` 文件夹拷到 `~/.claude/skills/kb-bot/`（Windows：`%USERPROFILE%\.claude\skills\kb-bot\`）
2. `agents/kb-bot.md` 拷到 `~/.claude/agents/kb-bot.md`
3. 重开会话即生效

卸：删掉上面两处即净卸。库数据在 `skills/kb-bot/kb/` 里——只想换 bot 不想丢库，就只删 agents 那个文件。

## 路由（一句话）

- 问"是什么/为什么/有什么坑"（机制）→ 交给 kb-bot agent：读库直答，答案带来源 + verified 日期
- 问"现在多少/现在什么样"（时效）→ agent 按 fast 节点的菜谱现查，答案带"截至 X 日 X 时"，数值不落库
- 库里没有 → 懒吸收：公开静态页直接 WebFetch；SPA/登录墙用 `tools/fetch-url.js`（本地 Chrome 渲染）取，答完落节点、更新 INDEX
- 不给没人问的领域预蒸——库跟着真实问题长，哪个领域问得多了再批量补

## 库结构

```
kb/<领域>/INDEX.md        一行一个节点（slug · 档位 · 一句话钩子），回答前先读它
kb/<领域>/<slug>.md       一个知识点一个文件，正文用 [[slug]] 链邻居（命中即一跳带出）
kb/<领域>/log.md          操作日志，一行一事（日期 | 动作 | 说明），落/改节点后追加
```

三档（写法唯一源在 agents/kb-bot.md）：

| 档 | 半衰期 | 存什么 |
|---|---|---|
| slow | 按年 | 机制/坑/铁律，存结论直答 |
| medium | 按月 | 口径/位置/规则，存结论 + verified，超 90 天回答带"老口径，用前复核" |
| fast | 按天 | 数值永不入库，只存菜谱（怎么查）；现查后更新"上次快照" |

## 防腐（生死线，不是附加功能）

- verified 日期必填；回答时超 90 天必须带复核提示
- fast 节点现查结果与"上次快照"对不上 → 节点标"待复核"，下次先验菜谱再用
- 分歧不抹平：官方口径和实测打架，写"对照"两行，别平均

## 新开一个领域

1. 直接问该领域的问题，agent 建域文件夹并落第一个节点（INDEX/log 首行模板在 agents/kb-bot.md）
2. 之后正常问，库自己长；没人问的领域不预建

## 工具（零依赖，纯 Node 内置模块）

- `tools/check-kb.js` 校验全库（结构/字段/verified/链接/INDEX 双向/ASCII 名），发布前必跑
- `tools/fetch-url.js` SPA/登录站抓取：本地 Chrome headless 渲染后取正文+链接；`--headful-login` 先真人登录（同 profile 下次免登）

## 红线

- 没有来源就不落库、不回答，绝不编
- 本包发布内容零客户数据：只记公开平台的用法与坑，不带任何客户业务数据、账号、名单
- 节点文件名全 ASCII（zip/跨平台安全），内容中文随意

## 声明

- 本 skill 按「现状」提供（MIT 许可），作者不对使用结果作任何保证。
- 本包是非官方开源工具，与任何平台厂商无关联；文中如提及第三方产品名称，均为对应公司商标，仅作说明性引用
- 本包不带任何知识数据出厂：kb/ 目录为空，库由装包人自己的问题长出来，存什么、怎么用，责任在装包人
- 知识有保鲜期，重要操作前按节点提示复核
- 库数据全在本机 `~/.claude/skills/kb-bot/kb/`，不联网上报
- 使用者自负合规责任：请遵守你所在平台的服务条款与当地法规；答案带来源与时间，重要决策请回原始出处核实
