# 创建行业 Persona（行业视角实例）

当用户请求**创建 / 新建 / 添加**行业视角（persona）时，走本流程，在 `references/industries/` 下生成新的 `{key}.md` 文件。

## 触发与解析

- **触发词**：创建行业、新建 persona、添加行业视角、create persona、add industry 等。
- **解析**：从用户消息中提取行业名称或拟用 key（如「金融科技」「fintech」）；若未给出，则通过对话询问一次确定 **显示名称** 与 **key**。
- **key 规则**：小写、英文、连字符，如 `fintech`、`ai-for-design`；中文名需转为拼音或英文 key。

## 创建步骤

1. **确定 key 与显示名**
   - 与用户确认：显示名称（报告标题用）、key（文件名，如 `fintech`）。
   - 若 key 已存在（`references/industries/{key}.md` 已存在），提示「该行业已存在，可改用其他 key 或编辑现有文件」。

2. **复制模板并填空**
   - 读取 `references/industries/_template.md`。
   - 按模板中的占位符逐段替换（见下方「模板占位说明」）；可向用户追问：报告标题句式、三条目名称、角色定位、检索侧重点、规则偏好等，或根据行业常识填写合理默认值。

3. **写入并校验**
   - 将填好的内容写入 `references/industries/{key}.md`。
   - 若存在 `references/industries/README.md`，在其「已支持行业」列表中追加本 key 与显示名。

4. **确认**
   - 回复用户：已创建 `references/industries/{key}.md`，并说明之后可用「用 [显示名] 视角 分析本月」或「分析 --persona={key}」调用分析。

## 模板占位说明（与 _template.md 对应）

| 占位符 / 区块 | 说明 | 示例 |
|---------------|------|------|
| `{DISPLAY_NAME}` | 行业显示名（报告标题用） | 金融科技 |
| `{KEY}` | 实例 key，小写连字符 | fintech |
| `{ALIASES}` | 用户可说哪些词映射到此 key | 金融科技、fintech、金融科技监管 |
| **报告覆盖 (A+B)** | 报告标题、三条目名称 | 见 ai-for-design.md |
| **角色 (Role)** | 本行业专家的人设与目标读者 | 1～2 段 |
| **检索与核查协议** | 本行业侧重的信源与过滤规则 | 可引用 verification-curation.md + 行业特有条款 |
| **规则 (Rules)** | 语言风格、条数上限、引用格式 | 与 output-format 一致 |
| **输出格式** | 单条动态的 Markdown 示例 | 与 template 一致，三条目名用本实例的 |

## 参考

- 现有完整示例：`references/industries/ai-for-design.md`
- 报告结构默认值：`assets/report-template.md`
- 核查与格式：`references/verification-curation.md`、`references/output-format.md`
