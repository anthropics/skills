# Platform Adapters

本目录包含将 Agent Skills 转换为不同平台格式的适配器工具。

## ⚠️ 重要说明

**这些适配器工具为理论性实现，尚未经过实际平台验证。**

- 转换脚本基于平台的一般特性和常见适配模式
- 生成的配置文件格式可能需要根据实际平台 API 调整
- **建议在实际使用前查阅目标平台的官方文档并进行测试**

## 支持的平台

- **Cursor** - 转换为 Cursor 自定义指令格式
- **Trae** - 转换为 Trae 插件格式
- **Qoder** - 转换为 Qoder Agent 格式
- **CodeBuddy** - 转换为 CodeBuddy Workflow 格式
- **Windsurf** - 转换为 Windsurf Cascade Skills 格式

## 快速开始

### 转换所有技能到所有平台

```bash
cd adapters
python convert_all.py ../skills ../adapters-output
```

### 转换单个平台

#### Cursor

```bash
cd adapters/cursor
python convert_to_cursor.py --all ../../skills ../../adapters-output/cursor
```

#### Trae

```bash
cd adapters/trae
python convert_to_trae.py --all ../../skills ../../adapters-output/trae
```

#### Qoder

```bash
cd adapters/qoder
python convert_to_qoder.py --all ../../skills ../../adapters-output/qoder
```

#### CodeBuddy

```bash
cd adapters/codebuddy
python convert_to_codebuddy.py --all ../../skills ../../adapters-output/codebuddy
```

#### Windsurf

```bash
cd adapters/windsurf
python convert_to_windsurf.py --all ../../skills ../../adapters-output/windsurf
```

## 目录结构

```
adapters/
├── README.md                    # 本文件
├── convert_all.py              # 主转换工具（转换到所有平台）
├── cursor/                     # Cursor 适配器
│   ├── README.md
│   └── convert_to_cursor.py
├── trae/                       # Trae 适配器
│   ├── README.md
│   └── convert_to_trae.py
├── qoder/                      # Qoder 适配器
│   ├── README.md
│   └── convert_to_qoder.py
├── codebuddy/                  # CodeBuddy 适配器
│   ├── README.md
│   └── convert_to_codebuddy.py
└── windsurf/                   # Windsurf 适配器
    ├── README.md
    └── convert_to_windsurf.py
```

## 输出格式

转换后的文件将保存在 `adapters-output/` 目录下，按平台分类：

```
adapters-output/
├── cursor/
│   └── .cursor/
│       └── rules/
│           ├── course-designer.md
│           ├── code-generator.md
│           └── ...
├── trae/
│   ├── course-designer/
│   │   ├── trae-plugin.json
│   │   └── SKILL.md
│   └── ...
├── qoder/
│   ├── course-designer-agent/
│   │   ├── qoder-agent-config.json
│   │   ├── SKILL.md
│   │   └── course_designer_agent.py
│   └── ...
└── codebuddy/
    ├── course-designer/
    │   ├── manifest.json
    │   ├── workflows/
    │   └── skills/
    └── ...
└── windsurf/
    ├── course-designer/
    │   ├── SKILL.md
    │   └── ...
    └── ...
```

## 依赖要求

转换脚本需要以下 Python 包：

```bash
pip install pyyaml
```

## 使用示例

### 示例 1: 转换单个技能到 Cursor

```bash
cd adapters/cursor
python convert_to_cursor.py ../../skills/course-designer .cursor/rules/
```

### 示例 2: 转换所有技能到 Qoder

```bash
cd adapters/qoder
python convert_to_qoder.py --all ../../skills qoder-agents/
```

### 示例 3: 转换所有技能到所有平台

```bash
cd adapters
python convert_all.py ../skills ../adapters-output
```

## 验证状态

| 平台 | 转换脚本 | 格式验证 | 平台验证 |
|------|---------|---------|---------|
| Cursor | ✅ 完成 | ⚠️ 需要验证 | ⚠️ 需要验证 |
| Trae | ✅ 完成 | ⚠️ 需要验证 | ⚠️ 需要验证 |
| Qoder | ✅ 完成 | ⚠️ 需要验证 | ⚠️ 需要验证 |
| CodeBuddy | ✅ 完成 | ⚠️ 需要验证 | ⚠️ 需要验证 |
| Windsurf | ✅ 完成 | ⚠️ 需要验证 | ⚠️ 需要验证 |

## 贡献

如果你验证了某个平台的适配方案，欢迎贡献：

1. 测试转换脚本生成的输出
2. 在实际平台上验证功能
3. 报告问题和改进建议
4. 提交 Pull Request

## 注意事项

- 转换脚本会自动提取 `SKILL.md` 中的 frontmatter 和内容
- 脚本会尝试提取工作流步骤，但可能需要手动调整
- 生成的配置文件格式可能需要根据实际平台 API 调整
- 建议在实际使用前查阅目标平台的官方文档

## 参考资源

- [Agent Skills 规范](https://agentskills.io/)
- [Cursor 文档](https://docs.cursor.com/)
- [Qoder 官网](https://qoder.com/)
- 各平台官方文档
