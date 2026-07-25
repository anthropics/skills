#!/usr/bin/env python3
"""
将「项目文档管理」规范插入全局 AI 指令文件真身，支持版本检测与自动升级。

用法：python3 insert_doc_governance.py <真身路径>

幂等行为：
- 若文件已含当前版本 → 跳过。
- 若文件含旧版本（或无版本标记的旧章节）→ 自动替换为新版。
- 若无「项目文档管理」章节 → 插入。

插入位置：文件末尾的 @RTK.md 等 @ 引用行之前；若无则追加到末尾。

版本升级方式：修改 STANDARD 后将 CURRENT_VERSION +1 即可；
下次 doc-init 运行时会自动检测并升级已部署的旧版本。
"""

import sys
import re

CURRENT_VERSION = 5

STANDARD = f"""## 项目文档管理
<!-- doc-governance-version: {CURRENT_VERSION} -->

### 1. 核心规则

* 根 `AGENTS.md` 是项目文档唯一一级入口；长期文档必须能从根 `AGENTS.md` 一跳或两跳找到。
* 涉及业务规则、架构机制、故障修复、跨模块影响或不熟悉领域时，先检索相关项目文档，再动手。
* **评审 / 审视 / 分析类任务**：相关规范是评判基准，必须先读完再下结论，不得因当前代码未使用某技术就跳过——评审恰恰要发现"该用却没用"的缺失项。
* 禁止用内置记忆功能，需要持久化的知识必须写入项目文档。
* 除 `README.md` 外，所有项目文档默认使用中文。
* 项目根 `CLAUDE.md` 默认只能保留一行：`@AGENTS.md`
* 新建或首次接手项目时，检查全局 AI 指令文件中是否声明了跨项目技术规范文档的位置；声明存在时按项目主语言/技术栈查找匹配文档，找到则在项目根 `AGENTS.md` 顶部建立引用（未声明该位置约定则跳过，不臆造路径）。

### 2. 文档导航

项目根 `AGENTS.md` 必须包含「文档导航」章节，登记项目内所有长期文档。

导航规则：

* 每条文档导航一行，包含路径和用途。
* 用途必须写成「什么时候该读」，覆盖该领域的全部任务类型（改/新建/评审/排查），不要只描述「它是什么」。
* 触发条件按「任务类型 / 业务领域」门控（如「改/评审 X 模块时」），不要按「代码是否已用到某具体技术」门控（如「涉及 Liquid Glass 时」）——后者对评审任务会失效：被评审的代码可能完全没用该技术，模型会判定"条件不满足"而跳过，恰恰漏掉了最该被发现的"该用却没用"问题。
* 文档指针尽量就近贴在它支撑的那条规则旁，不要只放在底部导航表里。

示例：

```md
- `docs/BILLING_KNOWLEDGE_BASE.md`：改、评审或排查订阅、支付、额度扣减、账单状态流转前必读。
- `docs/AUTH_PERMISSION_GUIDE.md`：开发、评审或修改用户登录、权限控制前必读。
```

```text
<项目根>/
├── AGENTS.md
├── CLAUDE.md
└── docs/
    ├── *_KNOWLEDGE_BASE.md（领域知识库）
    ├── *_GUIDE.md（领域指南）
    ├── ...
    ├── design/
    ├── troubleshooting/
    └── ...
```

### 3. 二级索引

默认不建二级索引，优先让根 `AGENTS.md` 直接导航到具体文档。

当某类文档过多，继续平铺会影响根 `AGENTS.md` 阅读时，才建立二级索引，例如：

```text
- `docs/troubleshooting/TROUBLESHOOTING_INDEX.md`: 排查任何故障 / 报错 / 异常行为前必读，先查有无同类前例
- `docs/reviews/REVIEW_INDEX.md`: review 或大改某模块前必读：先看历史 review 结论和遗留风险
```

建立二级索引后，根 `AGENTS.md` 只保留索引入口，明细下沉到二级索引；不得出现三级以上索引链路。

### 4. 文档变更

* 新增文档：同步登记到根 `AGENTS.md`。
* 删除文档：同步移除根 `AGENTS.md` 中的导航。
* 迁移或重命名文档：搜索全仓引用并同步更新。
* 新增长期文档类型：同步在根 `AGENTS.md` 说明用途、位置和进入路径。

### 5. 单一来源

* 一个概念、规则、机制只维护一个权威来源。
* 其他文档需要引用该内容时，用相对路径链接，不要复制粘贴。
* 权威结论或主称谓一旦经确认更新，所有引用旧结论 / 旧叫法的文档必须同步改正，不允许两份文档在任一时刻对同一件事给出矛盾结论。无法当场判定哪份对时，回到权威源（产品 / 需求文档、代码）核实原文，仍定不了则标「待确认」，不要放任矛盾留存。

### 6. 什么该记录

应该记录：

* 项目级行为规范、约束、强制流程。
* 项目业务规则、架构机制、领域知识。
* 代码变动导致变化的设计、流程、配置说明。
* 可复用的故障原因、排查路径、修复方式。
* Review 中形成的长期结论、风险点、后续约束。

不应该记录：

* 代码本身已经清楚表达的信息。
* `git log` / `git blame` 能查到的历史。
* 一次性现象。
* 只对当前会话有用、未来不会复用的信息。
* 已在其他文档记录过的规则。

### 7. 收工前检查

任务结束前检查：

* 承诺要写的文档是否已完成。
* 新增文档是否已登记到根 `AGENTS.md`。
* 删除、迁移、重命名文档后，旧引用是否已清理。
* 本次任务发现的新业务规则、设计机制、踩坑经验是否已落盘到文档。

会话结束前判断是否有需落盘的内容：

| 信息类型 | 目标位置 |
|---|---|
| 跨项目通用模式 / 检查清单 / 脚本 | 对应 skill 文件 |
| 项目级行为规范 / 约束 / 强制流程 | 项目根 `AGENTS.md` |
| 项目业务规则 / 架构 / 领域知识 / 代码变动导致已有文档失效 | `docs/` 中的文档 |
"""

VERSION_RE = re.compile(r"<!--\s*doc-governance-version:\s*(\d+)\s*-->")
SECTION_RE = re.compile(r"(^|\n)(## 项目文档管理\b.*?)(?=\n## |\Z)", re.S)


def _get_installed_version(content: str) -> int | None:
    """返回文件中已安装的版本号，无版本标记时返回 None。"""
    m = VERSION_RE.search(content)
    return int(m.group(1)) if m else None


def _remove_section(content: str) -> str:
    """删除现有的「项目文档管理」章节（含内容直到下一个同级 ## 标题或文件末尾）。"""
    # 匹配从 ## 项目文档管理 到下一个 ## 同级标题（或文件末尾）
    pattern = re.compile(
        r"\n## 项目文档管理\b.*?(?=\n## |\Z)", re.S
    )
    return pattern.sub("", content)


def insert(path: str) -> None:
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()

    installed = _get_installed_version(content)

    if installed is not None and installed >= CURRENT_VERSION:
        print(f"[跳过] 「项目文档管理」已是最新版本（v{installed}）：{path}")
        return

    if "## 项目文档管理" in content:
        if installed is None:
            print(f"[升级] 检测到无版本标记的旧章节，替换为 v{CURRENT_VERSION}：{path}")
        else:
            print(f"[升级] v{installed} → v{CURRENT_VERSION}：{path}")
        content = _remove_section(content)
    else:
        print(f"[新增] 插入「项目文档管理」v{CURRENT_VERSION}：{path}")

    # 找插入点：第一个以 @ 开头的行（@RTK.md 等引用）之前
    m = re.search(r"\n(@\S+.*)", content)
    if m:
        insert_pos = m.start()
        before = content[:insert_pos]
        after = content[insert_pos:]
        new_content = before.rstrip("\n") + "\n\n" + STANDARD.rstrip("\n") + "\n\n" + after.lstrip("\n")
    else:
        new_content = content.rstrip("\n") + "\n\n" + STANDARD.rstrip("\n") + "\n"

    with open(path, "w", encoding="utf-8") as f:
        f.write(new_content)

    print(f"[完成] 写入成功：{path}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"用法：python3 {sys.argv[0]} <AI 指令文件真身路径>", file=sys.stderr)
        sys.exit(1)
    insert(sys.argv[1])
