# AdFlow

信息流广告 AI Agent 自动剪辑系统 — 素材管理 · Agent 决策 · 投放闭环 · 自动优化

## 快速开始

```bash
cd adflow
python main.py
```

## 目录

```
adflow/         # 核心包
  models.py     # 数据模型
  config_loader.py
  db/           # 数据库层
  agents/       # Agent Pipeline（Phase 2）
  engine/       # 剪辑引擎（Phase 1）
  api/          # 投放平台对接（Phase 3）
  gui/          # PyQt6 面板
main.py         # 入口
config.yaml     # 全局配置
requirements.txt
```

## 版本

v0.1.0 — Phase 0: 基础设施
