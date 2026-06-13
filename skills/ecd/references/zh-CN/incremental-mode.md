# 增量模式 `[v1.1]`

## 目的

对于已有 ECD bundle 的项目，支持增量修改而无需重走完整的流水线。适用于对已冻结交接包的有限范围变更。

## 入场条件

- ECD bundle 已存在，含 `00-overview.md` 和 `90-code-handoff.md`
- 用户请求的是具体的、有限范围的变更（非完整重写）
- 变更不会使 bundle 的基础架构失效

## 检测规则 `[v1.2]`

增量模式检测在复杂度分类器**之前**自动运行：

1. 检查目标路径是否存在 ECD bundle（`00-overview.md` + `90-code-handoff.md`）
2. **如果存在 bundle** → 主动提示用户选择：
   ```
   🤖 ECD：[增量模式] 检测到已有 ECD bundle。
       是否使用增量模式？（仅更新变更部分，Token ~10k-15k）
       回复"是"或直接描述变更 → 增量模式
       回复"否"或"完整流程" → 正常分类器
   ```
3. 用户确认"是"或请求包含增量信号词（update、modify、change、add to existing、修改、增加、调整、更新）→ 进入增量模式，跳过分类器
4. 用户确认"否"或请求明显是完整重写 → 继续正常分类器流程
5. 无 bundle → 直接进入分类器，不做提示

## 流程

### 1. 评估变更影响

读取已有 bundle 的 `00-overview.md` 和 `90-code-handoff.md`。判断变更影响了哪些冻结决策：

| 变更类型 | 重入阶段 | 示例 |
|---------|---------|------|
| 影响产品语义 | Stage A (preprocess) | 用户说"改成支持多用户"（原本是单用户） |
| 影响实现但不影响语义 | Stage C (requirements) | 用户说"数据库从 SQLite 换成 PostgreSQL" |
| 纯增量功能（在现有架构内） | Stage J (compile) | 用户说"给登录页加个 loading spinner" |
| Bug 修复（语义已冻结） | 直接 `/code` | 用户说"登录按钮点两下会提交两次" |

### 2. 最小重跑

仅重跑重入点及之后的阶段：

- **重入 A**：重跑 A → （B-H 如有必要）→ J → code → achieve
- **重入 C**：重跑 C → （D-H 如有必要）→ J → code → achieve
- **重入 J**：仅重跑 J → code → achieve
- **直接 code**：更新 `97-code-preflight.md` → 执行变更 → achieve

### 3. 更新 Bundle

- 保留未被失效的所有阶段笔记
- 更新的笔记标记 `[INCREMENTAL UPDATE vN]`
- 追加而非替换 `05-constraint-ledger.md`
- 归档旧的 `Runs/<run-id>/` 记录（不删除）

### 4. 重新校验

- 运行 `python scripts/validate_ecl_bundle.py` 确认 bundle 完整性
- 验证 `code_ready=true` 依然成立
- 如果校验失败，指出需要修复的阶段

## 必须保留的内容

- 原始 `00-overview.md`（追加，不替换）
- 所有已归档的 `Runs/<run-id>/` 记录
- Bundle 目录结构

## 示例

### 示例 1：纯增量功能

```
用户："在现有的 ECD handoff 里给登录表单加个 loading spinner，
      API 调用期间显示。"

1. 读取已有 bundle → 这是纯增量，在现有架构内
2. 重入 Stage J (compile)：将 spinner 添加到 UI contract 和 file plan
3. 保留 Stage A-H 不变
4. 更新 90-code-handoff.md：新增一个实现单元
5. code → achieve
```

### 示例 2：语义变更

```
用户："之前的 todo 应用改成支持多用户。"

1. 读取已有 bundle → 这影响了产品语义（原本未定义多用户）
2. 重入 Stage A (preprocess)：重新澄清多用户相关语义
3. 运行必要的收敛阶段（B-H）
4. 重新编译交接包（J）
5. code → achieve
```

### 示例 3：Bug 修复

```
用户："修一下登录按钮点两下会提交两次的 bug。"

1. 读取已有 bundle → bug 修复不改变已冻结的语义
2. 直接进入 /code
3. 更新 97-code-preflight.md：记录 bug 修复
4. 验证 → achieve
```

## 与复杂度分类器的关系

增量模式在分类器**之前**运行。如果检测到增量模式条件，完全跳过分类器。不需要为增量修改重新评估复杂度等级——已有 bundle 的等级足够。
