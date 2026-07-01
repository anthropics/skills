# ECD 的理论谱系

## ECD 是什么

演进约束开发（Evolutionary Constraint Development，ECD）是一套围绕 Claude Code 工作方式构建出来的原创交付方法。它不是从某一篇论文、某一个框架或者某一条 prompt chain 直接照搬出来的，而是围绕一个硬约束拼出来的：

> 编码阶段绝不能被迫去发明高影响产品语义

整套系统都是从这个要求往外长出来的。

## 理论源头

ECD 的理论基础来自几类工程思想的组合。

### 1. 约束主导的规划

规划阶段把用户请求当成噪声很高的证据，而不是天然可信的真相。它的目标是尽量冻结足够多的约束，让后面的执行是忠实实现，而不是继续解释。

这直接体现在：

- `05-constraint-ledger.md` 作为共享真值面
- 规划阶段必须先消解隐藏假设，再允许编码
- 只要还有高影响缺口，就必须回流，而不是乐观推进

### 2. 分阶段编译

ECD 把交付看作一个编译链，而不是一场开放式长对话。原始请求会先被编译成 normalized case，再被编译成 staged bundle，再被编译成 code handoff，然后是 run evidence，最后才进入 achieve verdict。

这直接体现在：

- `pre -> plan -> code -> achieve`
- `code` 不允许把前面的 note 当成重新脑补产品的地方
- `90-code-handoff.md` 是编译产物，不是"阶段总结"

### 3. 面向实现交接的契约化设计

handoff 本身被设计成契约结构。它会冻结文件计划、函数契约、允许决定项、禁止决定项、验证命令、浏览器检查和回流触发器。

这直接体现在：

- `function_contracts`
- `implementation_units`
- `allowed_decisions` 与 `forbidden_decisions`
- `code_ready=true` 是一个真值声明，不是鼓励性标签

### 4. 编码前的对抗式审查

ECD 默认认为：任何由单个模型写出来的规划都容易被锚定、遗漏和乐观偏差污染。因此，在执行前必须通过 `Agent` 工具插入独立子 Agent 的攻击和审查。

这直接体现在：

- D 阶段独立 critique（`Agent` 工具启动）
- G 阶段 red-team 与 blue-team（两次独立 `Agent` 调用）
- H 阶段独立 coding-readiness review（`Agent` 工具启动）
- J 阶段独立 compile-for-code 判断（`Agent` 工具启动）

### 5. 以验收为中心的闭环

"能跑起来"不等于"完成了"。如果一轮执行虽然编译通过，但 first-open experience 明显坏掉，那就不能算 achieved。

这直接体现在：

- 单独存在的 `achieve` 阶段
- 可以归档，也可以诚实地拒绝归档
- 验收失败时 case 必须保持 open

## 为什么 ECD 要把这些东西合在一起

单看每一条思想都能帮忙，但都不够。

- 只有约束规划，没有阶段门，就会继续漂移
- 只有阶段门，没有契约，handoff 会写得很细但仍然模糊
- 只有契约，没有独立审查，会把错误更整齐地冻结下来
- 只有审查，没有 achieve，仍然可能把明显坏掉的结果说成 done

ECD 把它们组合起来，是为了让每个阶段卡住一种不同的失真来源。

## ECD 的核心命题

ECD 的核心命题可以概括成五条：

1. 原始请求不够可靠，不能直接拿来编码。
2. 规划必须在用户还可交互的时候尽量逼出真实语义。
3. 越往后走，允许解释的空间必须越小，而不是越大。
4. 真实子 Agent 是用来对抗父模型锚定偏差的，不是形式主义。
5. 闭环必须建立在证据上，而不是建立在"看起来差不多"上。

## ECD 不是什么

ECD 不是：

- 一个通用产品框架
- 对工程判断力的替代品
- 给小改动强行加厚文档的借口
- 认为所有工作流都必须经历同样多阶段

它是一个高纪律的交付闭环，专门用在语义漂移代价高的任务上。

## 为什么这个 Skill 明确是 Claude Code-first

这个 Skill 把方法和 Claude Code 绑在一起，是因为 Claude Code 恰好提供了 ECD 需要的几项关键能力：

- `Read`/`Glob`/`Grep`/`codegraph_*` 访问本地文件和代码图谱
- `Bash` 执行本地脚本和验证命令
- `Write`/`Edit` 编辑和维护分阶段产物
- `Agent` 启动真实独立子代理
- `TaskCreate`/`TaskUpdate` 跟踪实现进度
- `EnterPlanMode`/`ExitPlanMode` 结构化审批门

没有这些能力，ECD 仍然可以被描述，但很难被完整执行。
