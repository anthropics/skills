---
name: doc-compact
description: 文档整理与压缩。核心职责是在不丢行为信息的前提下压缩冗余文档——删复述、删死链、删历史沿革、收敛重复提醒；配套完成结构整理（纠正文档放置、重建根 AGENTS.md 索引、补 inline 指针、规范 CLAUDE.md 为单行 @*.md、判定并拆分过大项目的二级索引）和全局文档管理规范的检查/安装。当文档冗余膨胀、索引失效、AGENTS.md 膨胀、CLAUDE.md 混入杂质，或需要确认全局规范是否写清文档管理模式时使用。
---

# doc-compact

执行前先探测实际生效的文件，不硬编码路径。
`<DOC_INIT_DIR>` 默认与本 skill 同级：`<本 SKILL.md 所在目录>/../doc-init`

## 流程

**Step 1 校验全局规范 → Step 2 只读审计 → Step 3 判定二级索引 → Step 4 修复结构 → Step 5 压缩（核心，不可跳过）→ Step 6 验证**

---

## Step 1 — 全局规范

**目标文件仅限全局 AI 指令文件**，绝不能传项目 `AGENTS.md`：

```bash
# 探测全局 AI 指令文件真身（软链则跟到真身）
for f in ~/.claude/CLAUDE.md ~/.codex/AGENTS.md ~/.codex/instructions.md ~/.config/opencode/AGENTS.md; do
  [ -f "$f" ] && readlink -f "$f" 2>/dev/null || echo "$f"
done | sort -u
```

对每个存在的全局文件运行：`python3 <DOC_INIT_DIR>/scripts/insert_doc_governance.py <全局文件路径>`。
`[跳过]` = 已最新；`[新增/升级]` = 已写入，扫一遍其余章节删旧约定。
`<DOC_INIT_DIR>` 不存在时：逐条对照 `references/standard.md` 手工比对，报告中注明「未自动校验」。

**禁止**把当前项目的 `AGENTS.md` 传给 `insert_doc_governance.py`——项目 `AGENTS.md` 存放项目规范，不是全局 AI 指令文件，写入会污染项目文档。

## Step 2 — 只读审计

运行 `python3 scripts/audit.py [项目根]`，一次跑完机器可判的检查：

- **A** CLAUDE.md 全单行 `@*.md`
- **B** 无悬空 `@AGENTS.md`
- **C** 无裸 `OVERVIEW.md`/`INDEX.md`；具名 `<DOMAIN>_INDEX.md` 合法
- **D** AGENTS.md 行数（> 500 行 → Step 3）
- **E** 无孤儿文档（docs/specs 下未被根 AGENTS.md ∪ README ∪ `*_INDEX.md` 引用）
- **F** 文件命名合规（排查 `YYYY-MM-DD-*`，review `*-review.md`）
- **G** 预置折叠建议（排查 / Review 台账 ≥3 篇，建议性）
- **H** doc-init 联动：反向全局引用、领域地图段存在性 → **影响 Step 4/5 保护边界**
- **I** §2.5 路径存活性：对含 `§2.5 物理路径速查` 的 KB，`ls` 验证每行路径是否仍存在；STALE 路径纳入 Step 5 清理（详见 `compression-guide.md` §2.5 路径存活性验证）

人工补充检查：文档放置是否错位、是否冗余膨胀、是否存在易变事实跨文档复述（`grep -rn "具体数字" docs/`，命中 >2 处即疑似）。

### 受保护段

H 显示 `domain_map_present=True` 时，根 AGENTS.md 里的 `## 领域地图（doc-init）` 和 `## 待补充知识库（doc-init backlog）` 两段**原样保留**，不压缩、不折叠、不删除。

## Step 3 — 判定二级索引

默认单层平铺。**能不做就不做**——多一跳，漏读概率累加。

两条独立触发（满足其一即应折叠）：

**① 规模驱动**：导航占 AGENTS.md ≳ 1/2，或规则被挤到文件后半（主判据）；兜底：> 500 行且导航占相当篇幅。
拆法：根只保留「任务域索引入口」（每域一行），明细下沉到具名 `<DOMAIN>_INDEX.md`。

**② 类型驱动**：
- 排查记录 ≥3 篇 → 折叠到 `docs/troubleshooting/TROUBLESHOOTING_INDEX.md`
- Review 台账 ≥3 篇 → 折叠到 `docs/reviews/REVIEW_INDEX.md`
- 强路由须含「何时跳过 / 是否权威源」，不能只是干瘪文件名

## Step 4 — 修复结构

- **CLAUDE.md**：非单行 → 改回 `@AGENTS.md`；只剩注入块无内容 → 连同悬空 CLAUDE.md 一并删
- **文档命名/放置**：对齐规范（知识库/指南 `SCREAMING_SNAKE_CASE`，设计/review `kebab-case`，排查 `YYYY-MM-DD-*`）；移位/改名先列清单确认，再搜全仓引用同步
- **导航描述**：逐条检查是「何时该读」还是「它讲了什么」，后者路由效果差，改写为前者；触发条件覆盖全部任务类型（改/新建/评审/排查/优化）
- **索引重建**：只列真实文档，按领域聚类、高频在前；删死链/空占位；受保护段跳过
- **注入块/裸索引**：① 读块内容识别规则；② 对照 AGENTS.md 逐条判断是否已覆盖；③ 未覆盖的提炼后并入；④ 删整个注入块

## Step 5 — 压缩（核心交付，不可跳过）

**完整压缩判据和操作指南见 [`references/compression-guide.md`](references/compression-guide.md)**，执行前必读。

**不可静默跳过**：每篇 docs/specs 文档都必须逐篇过一遍判据。收工汇报必须给出逐篇账目（前 N 行 → 后 M 行，或「已审无可压，原因：xxx」）。

**执行分级**：
- **低风险，直接做**：复述 / 死链 / 历史沿革 / 空占位 / 重复提醒 / 行号引用（「第 N 行」「Line N」→ 先 Read 确认方法名，再替换为 `类名.方法名()` 锚定）/ 形式转化（叙述段→调用链/表格/决策表，信息不减只是换形式）（汇报列出即可）
- **高风险，先列清单确认**：删整篇、成段重写、拆并索引结构、删改含数字/边界条件正文、删 §0/§1.5/§2.5 章节

**漂移检查（文档已有压缩标识时）**：若文档已有 `<!-- 该文档整理/压缩于 YYYY-MM-DD -->` 且距今 < 30 天，默认跳过（报告中标"近期已压"）。若仍需压缩（代码变动导致新增内容），执行后额外检查：标识符是否被泛化、数字是否被抹除、因果链是否断裂、验证命令是否还能执行（详见 `compression-guide.md` 漂移风险章节）。

**压缩标识**：每篇处理完后，在文件真正末尾追加（或更新日期）：
`<!-- 该文档整理/压缩于 YYYY-MM-DD -->`
用脚本批量写入，见 compression-guide.md。

## Step 6 — 验证

```bash
python3 scripts/audit.py <项目根> --compact-date <今日 YYYY-MM-DD>
```

检查 I（压缩标识硬闸门）**必须 `压缩缺标识=0`** 才能收尾。任何缺标识文档 = 本轮漏审，补完重跑。
H 的 `domain_map_present` / `backlog_present` 不应因本次审计由 True 变 False。
审计项 I 的 STALE 路径若已在 Step 5 中清理，验证时应为 0；否则说明遗漏。

**§0 目录索引完整性**：含 KB 模板的文档（`*_KNOWLEDGE_BASE.md`）应有 `§0 目录索引`。缺失的在收尾报告中标注为"建议下次 doc-update 补充"，不阻塞本次收工。

---

## 安全边界

- **不裁定内容真相**：两份文档结论矛盾时，不自行判定谁对，报告里记录并请用户裁定
- **不碰**：第三方/vendored 项目、构建产物、备份目录、git worktree

## 参考文件

| 文件 | 何时读 |
|------|-------|
| [`references/compression-guide.md`](references/compression-guide.md) | Step 5 执行前：压缩判据、文档类型压缩力度表、高频陷阱与修复脚本 |
| [`references/standard.md`](references/standard.md) | Step 2 拿不准判定基准时：十一条标准完整说明、易变事实处理细则 |
| [`scripts/audit.py`](scripts/audit.py) | Step 2 / Step 6 自动审计脚本（Python 跨平台，兼容 Windows，替换原 audit.sh） |
