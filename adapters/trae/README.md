# Trae Adapter

将 Agent Skills 转换为 Trae 插件格式的适配器。

## 使用方法

### 转换单个技能

```bash
python convert_to_trae.py ../../skills/course-designer trae-plugins/
```

### 转换所有技能

```bash
python convert_to_trae.py --all ../../skills trae-plugins/
```

## 输出格式

转换后会创建 Trae 插件目录结构：

```
trae-plugins/
└── course-designer/
    ├── trae-plugin.json
    └── SKILL.md
```

## Trae 插件结构

每个 Trae 插件包含：

- `trae-plugin.json` - 插件清单文件，定义插件元数据和技能信息
- `SKILL.md` - 技能定义文件（从原技能复制）

## 在 Trae 中使用

1. 将插件目录复制到 Trae 的插件目录
2. 在 Trae 中注册插件
3. 激活所需的技能

## 注意事项

- ⚠️ 此适配方案为理论性建议，需要根据 Trae 平台的实际插件系统进行验证
- 建议查阅 Trae 官方文档了解插件格式要求
- 可能需要调整 manifest 格式以符合 Trae 的实际规范
