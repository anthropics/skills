---
name: regex-builder
description: Build, explain, and test regular expressions from natural language descriptions with multi-language code output. Use when user asks to create, explain, or test regex patterns.
license: MIT
---

# Regex Builder - 正则表达式构建与测试工具

## 触发条件

当用户提到以下关键词时激活：
- "写个正则"、"regex"、"正则表达式"、"regular expression"、"匹配模式"
- 需要文本匹配、提取、替换、验证的场景

### 模式自动识别

- "帮我写/构建一个正则来匹配 X" → 模式一（构建）
- "解释/分析这个正则：..." → 模式二（解释）
- "用这个正则测试/验证这段文本" → 模式三（测试）
- 默认进入模式一（构建模式）

## 三种工作模式

### 模式一：构建模式（自然语言 → 正则）

用户用自然语言描述需求，生成对应的正则表达式。

**执行流程：**

1. **理解需求**：确认要匹配的目标（什么内容、什么格式、哪些边界）
2. **确认语言**：询问目标语言（JS/Python/Go/Java），不同语言语法有差异
3. **生成正则**：输出正则表达式 + 逐段注释
4. **提供测试用例**：给出应匹配和不应匹配的样例
5. **生成代码片段**：直接可用的代码

**输出格式：**

```
## 正则表达式

/<pattern>/<flags>

## 逐段解释

- `<segment>` — 说明作用
- `<segment>` — 说明作用
...

## 测试用例

✅ 应匹配：
- `example1` → 匹配结果
- `example2` → 匹配结果

❌ 不应匹配：
- `counter-example1`
- `counter-example2`

## 代码片段

（根据目标语言生成）
```

### 模式二：解释模式（给正则 → 逐段解释）

用户给出一个正则表达式，逐字符/分组拆解含义。

**执行流程：**

1. **接收正则**：用户粘贴正则表达式
2. **拆解结构**：按字符、分组、量词、锚点逐段拆解
3. **整体总结**：用一句自然语言概括这个正则的作用
4. **指出潜在问题**：贪婪/非贪婪、回溯风险、性能陷阱
5. **提供改进建议**：如有更优写法则建议

**输出格式：**

```
## 整体含义

一句话概括这个正则的作用。

## 逐段拆解

| 片段 | 含义 | 类型 |
|------|------|------|
| `^` | 字符串开头 | 锚点 |
| `[a-z]` | 小写字母 | 字符类 |
| `+` | 一个或多个 | 量词 |
| ... | ... | ... |

## 分组结构

- 捕获组 1: `(...)` — 说明
- 非捕获组: `(?:...)` — 说明
- 命名组: `(?<name>...)` — 说明

## 潜在问题

- ⚠️ 问题描述及建议
```

### 模式三：测试模式（正则 + 文本 → 匹配结果）

用户给出正则和测试文本，展示匹配结果。

**执行流程：**

1. **接收输入**：正则 + 测试文本
2. **执行匹配**：展示每个匹配项及其位置
   - 位置展示格式：`[起始索引:匹配长度]`，例如 `[3:5]` 表示从索引 3 开始、匹配 5 个字符
3. **展示捕获组**：列出各捕获组的值
4. **边界测试**：自动补充边界情况测试
   - 自动生成以下边界输入进行测试：
     - 空字符串 `""`
     - 超长字符串（重复匹配模式至 10,000+ 字符）
     - 特殊字符输入（换行符 `\n`、制表符 `\t`、Unicode 字符、零宽字符等）

**输出格式：**

```
## 匹配结果

输入文本：`example test string 2024-01-15 and 2023-12-31`
正则：`/\d{4}-\d{2}-\d{2}/g`

| # | 匹配内容 | 起始索引 | 匹配长度 |
|---|----------|---------|---------|
| 1 | `2024-01-15` | 20 | 10 |
| 2 | `2023-12-31` | 35 | 10 |

## 捕获组

（如有捕获组，逐组列出值）

## 边界测试

| 测试输入 | 预期 | 结果 |
|---------|------|------|
| `""` (空字符串) | 不匹配 | ✅ 不匹配 |
| `"aaaa...(x10000)"` (超长) | 正常匹配/不匹配 | ✅ 无超时 |
| `"\n\t\0"` (特殊字符) | 不匹配 | ✅ 不匹配 |
```

---

## 常见正则模式速查表

### 邮箱

```
/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/
```

- ✅ `user@example.com`, `first.last+tag@sub.domain.org`
- ❌ `@example.com`, `user@`, `user@.com`

### URL

```
/^https?:\/\/(www\.)?[-a-zA-Z0-9@:%._+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b([-a-zA-Z0-9()@:%_+.~#?&/=]*)$/
```

- ✅ `https://example.com`, `http://sub.example.com/path?q=1`
- ❌ `ftp://example.com`, `example`, `://missing.com`

> **注意**：此版本不支持 IPv6 地址、端口号、用户名密码等完整 URL 格式。
> 如需完整验证，建议使用语言内置的 URL 解析器（如 `new URL()`）。

### 中国大陆手机号

```
/^1[3-9]\d{9}$/
```

- ✅ `13812345678`, `19900001111`
- ❌ `12345678901`, `1381234567`, `038123456789`

### IPv4 地址

```
/^((25[0-5]|2[0-4]\d|[01]?\d\d?)\.){3}(25[0-5]|2[0-4]\d|[01]?\d\d?)$/
```

- ✅ `192.168.1.1`, `0.0.0.0`, `255.255.255.255`
- ❌ `256.1.1.1`, `1.2.3`, `1.2.3.4.5`

### 日期（YYYY-MM-DD）

```
/^\d{4}-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])$/
```

- ✅ `2024-01-15`, `2023-12-31`
- ❌ `2024-13-01`, `2024-00-15`, `24-01-15`

### 中文字符

```
/[\u4e00-\u9fff]/
```

- ✅ `你好`, `中文测试`
- ❌ `hello`, `12345`

> **注意**：`\u4e00-\u9fff` 仅覆盖 **CJK 统一汉字基本区**（共 20,992 字），不包含扩展区字符。
> 扩展区 A（`\u3400-\u4DBF`）、扩展区 B（`\u{20000}-\u{2A6DF}`）等包含大量生僻字和古汉字。
> 若需匹配更完整的中文（含扩展区及兼容字符），建议使用 Unicode 属性：JS `/\p{Script=Han}/u`、Python `regex` 库的 `\p{Han}`、Go/Java `\p{Han}`。

### 强密码（8+ 位，含大小写字母、数字、特殊字符）

```
/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/
```

- ✅ `Passw0rd!`, `MyP@ss1234`
- ❌ `password`, `12345678`, `PASSWORD1!`

> `[@$!%*?&]` 是示例集合，实际应按业务需求调整。
> 常用扩展集合：`` !@#$%^&*()_+\-=\[\]{}|;:'",.<>?/~` ``

### 十六进制颜色

```
/^#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})$/
```

- ✅ `#fff`, `#a1B2c3`
- ❌ `#gg0000`, `fff`, `#12345`

---

## 语言语法差异对照表

| 特性 | JavaScript | Python | Go | Java |
|------|-----------|--------|-----|------|
| 正则字面量 | `/pattern/flags` | `r"pattern"` | `` `pattern` `` | `"pattern"` (需转义) |
| 命名捕获组 | `(?<name>...)` | `(?P<name>...)` | `(?P<name>...)` | `(?<name>...)` |
| 非贪婪量词 | `*?`, `+?`, `??` | `*?`, `+?`, `??` | `*?`, `+?`, `??` | `*?`, `+?`, `??` |
| 前瞻断言 | `(?=...)`, `(?!...)` | `(?=...)`, `(?!...)` | 不支持 | `(?=...)`, `(?!...)` |
| 后顾断言 | `(?<=...)`, `(?<!...)` | `(?<=...)`, `(?<!...)` | 不支持 | `(?<=...)`, `(?<!...)` |
| Unicode 属性 | `\p{L}` (需 `/u` 标志) | 不原生支持 | `\p{L}` | `\p{L}` |
| 反向引用 | `\1` 或 `\k<name>` | `\1` 或 `(?P=name)` | 不支持 | `\1` 或 `\k<name>` |
| 多行模式标志 | `/m` | `re.MULTILINE` | `(?m)` 内联标志 | `Pattern.MULTILINE` |
| 忽略大小写 | `/i` | `re.IGNORECASE` | `(?i)` 内联标志 | `Pattern.CASE_INSENSITIVE` |
| 全局匹配 | `/g` | `re.findall()` | `FindAllString()` | `matcher.find()` 循环 |
| 原始字符串 | 无（手动转义） | `r"..."` | `` `...` ``（天然原始） | 无（双重转义 `\\d`） |

---

## 目标语言选择

- 默认语言：JavaScript/TypeScript
- 如果用户未指定语言，根据当前项目上下文自动推断
- 如无法推断，生成 JavaScript 版本并询问是否需要其他语言
- 支持同时输出多语言版本（用户明确要求时）

---

## 代码生成模板

### JavaScript

```javascript
// 1. Compile pattern (literal syntax: /pattern/flags)
const regex = /your-pattern-here/gi

// 2. Match test
const isMatch = regex.test(input)

// 3. Extract first match
const match = input.match(regex)
if (match) {
  const fullMatch = match[0]       // full match
  const group1 = match[1]          // first capture group
}

// 4. Extract all matches (note: matchAll requires the g flag)
const allMatches = [...input.matchAll(/your-pattern-here/g)]
allMatches.forEach(m => {
  // m[0]: full match, m.index: start position
})

// 5. Replace
const result = input.replace(/your-pattern-here/gi, '<replacement>')

// 6. Named groups
const namedMatch = input.match(/(?<year>\d{4})-(?<month>\d{2})-(?<day>\d{2})/)
if (namedMatch?.groups) {
  const { year, month, day } = namedMatch.groups
}

// 7. Dynamic pattern via RegExp constructor (note: double escape \\d not \d)
const dynamic = new RegExp('\\d{4}-\\d{2}-\\d{2}', 'gi')
```

### Python

```python
import re

# 1. Compile pattern (recommended for repeated use)
pattern = re.compile(r"<pattern>", re.IGNORECASE)

# 2. Match test
if pattern.search(text):
    print("matched")

# 3. Extract first match
match = pattern.search(text)
if match:
    full = match.group(0)       # full match
    group1 = match.group(1)     # first capture group

# 4. Extract all matches
all_matches = pattern.findall(text)

# 5. Replace
result = pattern.sub("<replacement>", text)

# 6. Named groups
match = re.search(r"(?P<year>\d{4})-(?P<month>\d{2})-(?P<day>\d{2})", text)
if match:
    year = match.group("year")
```

### Go

```go
import "regexp"

// 1. Compile pattern (panics on invalid pattern)
re := regexp.MustCompile(`<pattern>`)

// 2. Match test
isMatch := re.MatchString(input)

// 3. Extract first match
match := re.FindString(input)

// 4. Extract first match with capture groups
submatch := re.FindStringSubmatch(input)
if len(submatch) > 1 {
    group1 := submatch[1]   // first capture group
}

// 5. Extract all matches
allMatches := re.FindAllString(input, -1)

// 6. Replace
result := re.ReplaceAllString(input, "<replacement>")

// 7. Named groups
re = regexp.MustCompile(`(?P<year>\d{4})-(?P<month>\d{2})-(?P<day>\d{2})`)
match2 := re.FindStringSubmatch(input)
if match2 != nil {
    yearIdx := re.SubexpIndex("year")
    year := match2[yearIdx]
}
```

### Java

```java
import java.util.regex.*;

// 1. Compile pattern (note: double escape \\d not \d in Java strings)
Pattern pattern = Pattern.compile("<pattern>", Pattern.CASE_INSENSITIVE);

// 2. Match test
Matcher matcher = pattern.matcher(input);
boolean isMatch = matcher.find();

// 3. Extract first match
matcher = pattern.matcher(input);
if (matcher.find()) {
    String fullMatch = matcher.group(0);    // full match
    String group1 = matcher.group(1);       // first capture group
}

// 4. Extract all matches
matcher = pattern.matcher(input);
while (matcher.find()) {
    System.out.println(matcher.group());
}

// 5. Replace
String result = pattern.matcher(input).replaceAll("<replacement>");

// 6. Named groups
Pattern datePat = Pattern.compile("(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})");
Matcher dateMatcher = datePat.matcher(input);
if (dateMatcher.find()) {
    String year = dateMatcher.group("year");
}

// 7. Full match validation (matches() requires entire string to match)
boolean fullMatch = Pattern.matches("^\\d{4}-\\d{2}-\\d{2}$", input);
```

---

## 边界情况与性能提醒

### 贪婪 vs 非贪婪

```
# 贪婪（默认）：尽可能多匹配
/<.*>/     对 "<a>text<b>" 匹配 "<a>text<b>" （整个字符串）

# 非贪婪：尽可能少匹配
/<.*?>/    对 "<a>text<b>" 匹配 "<a>" 和 "<b>" （分别匹配）
```

**规则**：当需要匹配最短内容时，始终使用非贪婪量词 `*?`, `+?`, `??`。

### 灾难性回溯（Catastrophic Backtracking）

以下模式可能导致指数级时间复杂度：

```
# 危险模式 — 嵌套量词
/(a+)+$/        对 "aaaaaaaaaaaaaaaaab" 极慢
/(a|a)+$/       同上
/(\d+)+$/       同上

# 安全替代
/a+$/           去掉嵌套量词
```

**规则**：
- 避免嵌套量词 `(x+)+`, `(x*)*`, `(x+)*`
- 避免交替中有重叠的模式 `(a|ab)+`
- 对用户输入的正则使用超时机制

### 锚点的重要性

```
# 无锚点 — 部分匹配
/\d{3}/        对 "abc123def" 匹配 "123"（可能非预期）

# 有锚点 — 完整匹配
/^\d{3}$/      对 "abc123def" 不匹配（预期行为）
```

**规则**：验证场景务必加 `^...$` 锚点。

### 字符类中的特殊字符

```
# 连字符在字符类中的位置
[a-z]          a 到 z 的范围
[a\-z]         a、- 或 z（转义连字符）
[-az]          -、a 或 z（放在开头）
[az-]          a、z 或 -（放在末尾）

# 方括号中不需要转义的字符
[.]            匹配字面量点号（不是任意字符）
[*+?]          匹配字面量 *、+ 或 ?
```

### 多行模式陷阱

```
# 默认模式
/^abc$/        只匹配整个字符串为 "abc"

# 多行模式
/^abc$/m       匹配任意一行为 "abc"（JS 的 m 标志）

# 注意：. 默认不匹配换行符
/.+/           对 "line1\nline2" 只匹配 "line1"
/.+/s          对 "line1\nline2" 匹配 "line1\nline2"（JS 的 s 标志 / Python 的 re.DOTALL）
```

---

## 质量检查清单

### 必须检查（生成后立即验证）：

- [ ] 正确匹配所有正面样例
- [ ] 正确排除所有反面样例
- [ ] 无灾难性回溯风险（嵌套量词检测）
- [ ] 锚点使用正确（`^`/`$` 或 `\b`）

### 强烈建议检查：

- [ ] 贪婪/非贪婪量词选择合理
- [ ] 目标语言兼容性确认
- [ ] 性能可接受（无过度回溯）

### 可选检查：

- [ ] 边界情况覆盖（空字符串、超长字符串、特殊字符）
- [ ] 正则可读性（复杂正则添加注释或使用 verbose 模式）
- [ ] 转义正确性（特殊字符转义、字符串中反斜杠双重转义）

---

## 错误处理

当遇到以下情况时：

1. **正则语法错误** → 指出具体位置，给出修复建议和正确示例
2. **灾难性回溯风险** → 标记 ⚠️ 警告，提供无回溯的替代方案
   - 示例：`(a+)+$` → 改为 `a+$`（原子组）或使用 possessive quantifier
3. **语言不支持的特性** → 明确告知限制并提供该语言的替代方案
   - 示例：Go 不支持前瞻断言 → 建议用代码逻辑替代
4. **需求模糊** → 主动询问用户提供更多正面/反面样例

---

## ⚠️ 安全考虑：ReDoS 防护

**正则表达式拒绝服务（ReDoS）** 是一种利用恶意输入使正则引擎陷入指数级回溯的攻击。

### 危险模式识别

以下模式存在 ReDoS 风险：
- 嵌套量词：`(a+)+`、`(a*)*`、`(a+)*`
- 重叠交替：`(a|a)+`、`(.*a){n}`
- 回溯陷阱：`^(a+)+$` 对不匹配的长字符串可达 O(2^n) 复杂度

### 防护建议

1. **避免嵌套量词** — 将 `(a+)+` 简化为 `a+`
2. **使用原子组/possessive quantifier** — 如 `(?>a+)` 或 `a++`（部分引擎支持）
3. **设置执行超时** — 对用户提供的正则限制执行时间（如 5 秒）
4. **限制输入长度** — 在应用正则前验证输入长度上限
5. **使用 RE2 等无回溯引擎** — Go 的 regexp 包天然免疫 ReDoS

> 对于处理不受信任输入的正则，**必须**检测上述危险模式。

---

## 复杂正则的可读性增强

### Python verbose 模式

```python
pattern = re.compile(r"""
    ^                   # start of string
    (?P<year>\d{4})     # 4-digit year
    -                   # separator
    (?P<month>0[1-9]|1[0-2])  # month 01-12
    -                   # separator
    (?P<day>0[1-9]|[12]\d|3[01])  # day 01-31
    $                   # end of string
""", re.VERBOSE)
```

### JavaScript 注释方式（拆分 + 拼接）

```javascript
const parts = [
  '(?<year>\\d{4})',      // 4-digit year
  '-',                     // separator
  '(?<month>0[1-9]|1[0-2])', // month 01-12
  '-',                     // separator
  '(?<day>0[1-9]|[12]\\d|3[01])', // day 01-31
]
const regex = new RegExp('^' + parts.join('') + '$')
```
