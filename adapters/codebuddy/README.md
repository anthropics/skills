# CodeBuddy Adapter

将 Agent Skills 转换为 CodeBuddy Workflow 格式的适配器。

## 使用方法

### 转换单个技能

```bash
python convert_to_codebuddy.py ../../skills/course-designer codebuddy-plugins/
```

### 转换所有技能

```bash
python convert_to_codebuddy.py --all ../../skills codebuddy-plugins/
```

## 输出格式

转换后会创建 CodeBuddy 插件目录结构：

```
codebuddy-plugins/
└── course-designer/
    ├── manifest.json
    ├── workflows/
    │   └── course-designer.json
    └── skills/
        └── course-designer/
            └── SKILL.md
```

## CodeBuddy 插件结构

每个 CodeBuddy 插件包含：

- `manifest.json` - 插件清单文件
- `workflows/` - 工作流定义目录
- `skills/` - 技能定义目录

## Workflow 格式

```json
{
  "id": "course-designer",
  "name": "Course Designer",
  "description": "Design courses and curricula",
  "steps": [
    {
      "id": 1,
      "name": "analyze",
      "description": "Analyze requirements",
      "type": "instruction"
    }
  ]
}
```

## 在 CodeBuddy 中使用

1. 将插件目录复制到 CodeBuddy 的插件目录
2. 在 CodeBuddy 中注册插件
3. 使用工作流执行技能任务

## 注意事项

- ⚠️ 此适配方案为理论性建议，需要根据 CodeBuddy 平台的实际功能进行验证
- Workflow 格式可能需要根据 CodeBuddy 的实际规范调整
- 建议查阅 CodeBuddy 官方文档了解支持的插件格式
