# Git History Mining

本文定义 `doc-init` 如何使用 Git 历史。Git 历史是高噪声弱信号：只能帮助发现热点、风险、历史叫法和 Q&A 追问，不是当前业务规则的权威来源。

## 使用目标

- 热点风险：高频变更目录、反复 fix / revert 的文件，提示后续生成 KB 时多找证据。
- 历史兼容：commit message 中的兼容、迁移、废弃、老数据、回滚、线上等线索，触发用户追问。
- 领域边界：经常共同变更的文件组，可辅助判断哪些代码可能属于同一业务域。
- 领域语言：commit message 是人类曾经使用过的叫法语料，可作为主称谓候选或历史别名。

## 禁止事项

- 不得仅凭 commit message 写当前业务规则。
- 不得把历史叫法直接升级为最终主称谓。
- 不得生成历史故障台账、排障历史或“曾经发生过什么”的正式文档。
- 默认不做全量历史扫描、`git blame`、PR/MR API 或 issue 系统深挖。

## 扫描方式

默认运行：

```bash
python3 <DOC_INIT_DIR>/scripts/git_history_miner.py --root . --output .doc-init-git-history.json
```

默认只扫描最近 300 条 commit。若正在生成某个领域 KB，且已经知道该领域路径，可窄范围扫描：

```bash
python3 <DOC_INIT_DIR>/scripts/git_history_miner.py --root . --paths src/customer service/customer --output .doc-init-git-customer.json
```

脚本失败、无 `.git`、空历史或浅克隆时不阻塞；在知识边界报告和自评里标注 Git 弱信号不可用或覆盖不足。

## 领域语言规则

完整主称谓优先级见 `knowledge-network-design.md`「领域语言统一」节。Commit message 中的叫法只能作为”团队曾经这么叫”的证据（优先级第 4 位），不得覆盖用户确认和核心文档。不要为普通别名生成术语表。

## 输出落点

Git 弱信号进入知识边界报告：

- 热点路径
- 历史叫法候选
- fix / revert / 兼容 / 迁移 / 废弃线索
- 与当前证据冲突处
- 应向用户确认的问题

只有当弱信号被当前代码、数据库、运行时证据或用户确认交叉验证后，才可以沉淀进领域 KB 或公共 Guide。

## Q&A 模板

- 领域语言：「Git 历史里多次叫 [A]，代码/表里叫 [B]，团队现在写需求和沟通时统一叫哪个？」
- 历史兼容：「历史提交多次提到 [兼容老数据/迁移/废弃]，当前代码里这个兼容逻辑还有效吗？AI 改这块时必须保留什么？」
- 热点风险：「[路径/文件] 最近反复 fix/revert，它是业务核心还是历史包袱？改这里最容易踩什么坑？」
- 共同变更：「这些文件经常一起改：[A, B, C]。它们是否属于同一业务流程？生成 KB 时应该合并还是拆开？」
