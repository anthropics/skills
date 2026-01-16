# Cursor Adapter

将 Agent Skills 转换为 Cursor 自定义指令格式的适配器。

## 使用方法

### 转换单个技能

```bash
python convert_to_cursor.py ../../skills/course-designer .cursor/rules/
```

### 转换所有技能

```bash
python convert_to_cursor.py --all ../../skills .cursor/rules/
```

## 输出格式

转换后的文件将保存在 `.cursor/rules/` 目录下，格式为 `{skill-name}.md`。

## 在 Cursor 中使用

### 方法一：项目级规则

将转换后的文件放在项目根目录的 `.cursor/rules/` 目录下：

```
my-project/
├── .cursor/
│   └── rules/
│       ├── course-designer.md
│       └── code-generator.md
└── src/
```

### 方法二：全局规则

将转换后的文件放在 Cursor 的全局配置目录：

```bash
# macOS/Linux
~/.cursor/rules/

# Windows
%APPDATA%\cursor\rules\
```

### 方法三：项目上下文

将技能目录复制到项目中，Cursor 会自动读取：

```
my-project/
├── skills/
│   ├── course-designer/
│   │   └── SKILL.md
│   └── code-generator/
│       └── SKILL.md
└── .cursorignore
```

## 注意事项

- Cursor 会自动读取 `.cursor/rules/` 目录下的 Markdown 文件
- 确保文件编码为 UTF-8
- 文件名使用 kebab-case 格式
