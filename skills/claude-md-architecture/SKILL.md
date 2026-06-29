---
name: claude-md-architecture
description: Teaches the SOUL/INTERFACE/BODY three-layer architecture for CLAUDE.md files — isolates model-specific tuning from identity and process rules. Use when switching between LLMs (Claude, DeepSeek, Gemini, Qwen) to avoid config drift.
version: 1.0.0
tags: [configuration, architecture, multi-model, claude-code, methodology]
---

# Claude.md Architecture Skill

## Description

Teaches the SOUL/INTERFACE/BODY three-layer architecture for structuring CLAUDE.md and its companion files. This pattern separates configuration into three independent layers, making model swaps trivial: when you change LLMs, you rewrite one file instead of everything.

**Universal use case:** Anyone who switches between LLMs (Claude ↔ DeepSeek ↔ Gemini ↔ Qwen) faces config drift — behavior rules mixed with identity statements. This skill teaches a pattern that isolates model-specific tuning from identity and process rules.

**No specific LLM required.** The pattern works for any AI coding agent with a configuration file. Templates are generic; users adapt them to their own stack.

## The Three Layers

### SOUL.md — Identity Layer

What stays constant across models:
- Who you are (role, expertise, goals)
- What you're trying to achieve (short-term and long-term)
- How you grow (learning methodology, feedback loops)
- External capabilities you can access (skills, MCP servers, memory)

**Rule:** SOUL.md never changes when you switch models. Identity is model-independent.

### INTERFACE.md — Calibration Layer

What changes per model:
- Model-specific behavioral quirks to compensate for
- Performance characteristics (context window, attention patterns)
- Tool-calling precision and reliability
- Output tendencies (verbosity, formatting, language preference)

**Rule:** This is the ONLY file you rewrite when switching models. It's thin — just the calibration parameters that differ between LLMs.

### BODY.md — Process Layer

How work gets done:
- Session startup and shutdown sequences
- Review and quality gate procedures
- Token efficiency rules
- Learning capture and knowledge management
- Error handling and escalation paths

**Rule:** BODY.md is model-independent but reads INTERFACE.md's calibration to adjust behavior. It's the execution engine.

## Architecture Flow

```
CLAUDE.md (orchestrator)
    ↓
self-model.md ← 先看见自己
    ↓
SOUL.md ← 身份·目标·成长·能力注册
    ↓
INTERFACE.md ← 大脑校准·神经调控
    ↓
BODY.md ← 身体规则·受INTERFACE调控
    ↓
写回 self-model.md ← 闭环
```

## When to Use

- Setting up a new AI coding agent configuration
- Switching between LLM providers and avoiding config drift
- Designing a config system that needs to survive model changes
- Teaching others how to structure their CLAUDE.md files

## Quick Start

1. Create `SOUL.md` — define your identity and goals (model-independent)
2. Create `INTERFACE.md` — calibrate for your current model
3. Create `BODY.md` — define your process rules (reads INTERFACE for tuning)
4. Wire them together: CLAUDE.md loads all three in sequence

## Templates

### SOUL.md Template
```markdown
# SOUL
> 我是谁·我要去哪·我怎么长大

## 身份
- [Your role, expertise level, domain]

## 目标
- 短期: [immediate goals]
- 长期: [long-term vision]

## 成长
- [How you learn, feedback mechanisms]

## 能力
- [Available tools, skills, memory systems]

## 便携
换LLM只换INTERFACE.md · 灵魂和记忆保持不变
```

### INTERFACE.md Template
```markdown
# INTERFACE
> 灵魂-大脑接口 · 换LLM只换此文件

## 当前大脑
- 模型: [model name and version]
- [Model-specific parameters]

## 行为校准
- [Compensations for model quirks]
- [Output constraints]

## 神经系统
| 大脑特征 | 身体调控 |
|---------|---------|
| [模型特点] | [对应的BODY调整] |
```

### BODY.md Template
```markdown
# BODY
> 流程规则 · 受INTERFACE神经系统调控

## 启动检查
- [Session startup procedures]

## 收尾铁律
- [Session shutdown and quality gates]

## 三层审查
- [Review procedures]
```

## Key Principles

1. **One file changes per model swap.** Only INTERFACE.md.
2. **SOUL is the anchor.** If your identity changes, update SOUL. Otherwise hands off.
3. **BODY reads INTERFACE.** Process rules adapt to model characteristics automatically.
4. **Portable.** This architecture works for any AI coding agent with configuration files.

## Pitfalls

- Don't put model-specific tuning in BODY.md — it belongs in INTERFACE
- Don't put identity statements in INTERFACE — they belong in SOUL
- Don't make INTERFACE too thick — it should be the thinnest file
- Templates are starting points — customize for your stack

## See Also

- `skill-creator` — How to write skills that work with this architecture
- `self-audit` — Quality gate that works across models
- `delivery-gate` — Stop hook for learning capture enforcement
