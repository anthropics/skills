# Qoder Adapter

将 Agent Skills 转换为 Qoder Agent 格式的适配器。

## 使用方法

### 转换单个技能

```bash
python convert_to_qoder.py ../../skills/course-designer qoder-agents/
```

### 转换所有技能

```bash
python convert_to_qoder.py --all ../../skills qoder-agents/
```

## 输出格式

转换后会创建 Qoder Agent 目录结构：

```
qoder-agents/
└── course-designer-agent/
    ├── qoder-agent-config.json
    ├── SKILL.md
    └── course_designer_agent.py
```

## Qoder Agent 结构

每个 Qoder Agent 包含：

- `qoder-agent-config.json` - Agent 配置文件，定义 agent 的能力和工作流
- `SKILL.md` - 原始技能定义文件
- `{skill_name}_agent.py` - Python Agent 模块（可选）

## Agent 配置格式

```json
{
  "name": "course-designer-agent",
  "description": "Agent for designing courses",
  "version": "1.0.0",
  "type": "skill-agent",
  "capabilities": ["course-design", "curriculum-planning"],
  "workflow": [
    {
      "step": "analyze-requirements",
      "description": "Analyze course requirements"
    }
  ],
  "instructions": "SKILL.md"
}
```

## 在 Qoder 中使用

1. 将 agent 目录部署到 Qoder 可访问的位置
2. 在 Qoder 中注册 agent
3. 配置 agent 的权限和依赖
4. 激活 agent 并开始使用

## 注意事项

- ⚠️ 此适配方案基于 Qoder 作为 agentic platform 的特性，需要根据实际 API 验证
- Agent 配置格式可能需要根据 Qoder 的实际规范调整
- Python agent 模块为示例代码，需要根据 Qoder 的 SDK 进行调整
- 建议查阅 [Qoder 官方文档](https://qoder.com/) 获取最新信息
