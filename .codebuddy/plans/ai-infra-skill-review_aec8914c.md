---
name: ai-infra-skill-review
overview: 全面审查 ai-infra skill 的 95 个 Markdown 文件，修复事实错误、数值不一致、过时 API，并补充缺失的关键主题和示例。
todos:
  - id: fix-training-fundamentals
    content: 修复 00-training-fundamentals 领域的事实错误：Softmax 数值、FFN 参数、GPU 费用、GPT-4 PPL、README 时间矛盾、warmup 代码，使用 [subagent:code-explorer] 精确定位
    status: completed
  - id: fix-gpu-hardware
    content: 修复 01-gpu-hardware 领域的硬件规格错误：Volta INT8 标记、Register File 大小、B100 型号、架构识别代码、消费级 GPU TFLOPS、TCO 分水岭、能效比对比口径
    status: completed
  - id: fix-distributed-training
    content: 修复 02-distributed-training 领域的数值一致性：将所有文件的 AdamW 优化器显存统一为 84GB、修正训练年限估算、统一符号体系、更新 torch.distributed.launch 为 torchrun
    status: completed
  - id: fix-mlops-and-cluster
    content: 修复 04-mlops-llmops 过时 API（MLflow Alias、Feast Field、Evidently 路径）和 05-cluster-scheduling PromQL 错误及 Kueue 描述
    status: completed
  - id: update-deprecated-apis
    content: 全局更新过时 PyTorch API：torch.cuda.amp 替换为 torch.amp，涉及 01-gpu-hardware、02-distributed-training、06-learning-roadmap 共 6 个文件
    status: completed
  - id: add-missing-topics
    content: 新增关键缺失主题文件：02-distributed-training/14-activation-checkpointing.md（激活重计算）和 00-training-fundamentals/13-gradient-accumulation.md（梯度累积与评估指标），并更新对应的 README 索引，使用 [skill:skill-creator] 确保规范
    status: completed
    dependencies:
      - fix-distributed-training
      - fix-training-fundamentals
  - id: sync-index-and-skill
    content: 同步更新各领域 README 索引和 SKILL.md 主入口：精简索引文件冗余内容、补充新文件导航链接、确保跨文件引用一致
    status: completed
    dependencies:
      - fix-training-fundamentals
      - fix-gpu-hardware
      - fix-distributed-training
      - fix-mlops-and-cluster
      - add-missing-topics
---

## 用户需求

对 `skills/ai-infra/` 目录下的 AI Infrastructure 学习框架进行全面 Review 并修复，覆盖 SKILL.md 主入口 + 8 个主题领域（含 8 个索引文件 + 约 87 个子文件）。

## 产品概述

这是一个系统性的 AI 基础设施知识文档库（Skill），涵盖训练基础、GPU 硬件、分布式训练、推理部署、MLOps、集群调度、学习路线图、知识库/RAG 等 8 大领域。本次 Review 需修复事实错误、更新过时内容、统一跨文件数据一致性、补充缺失的关键主题。

## 核心特性

### 一、修复严重事实错误（27 处已确认）

- 修正数学计算错误（Softmax 数值、AdamW 显存计算、TCO 分水岭等）
- 修正硬件规格错误（Volta INT8 Tensor Core、Register File 大小、B100 型号、消费级 GPU TFLOPS）
- 修正代码逻辑错误（NVIDIA 架构识别代码、CosineAnnealingLR + warmup 组合）
- 修正数据估算错误（单 A100 训练 GPT-3 时长、GPU 费用、GPT-4 PPL）
- 修正 PromQL 错误（`increase()` 用于 gauge、错误的指标名）
- 修正不准确表述（Kueue 定位、能效比不可比数据）

### 二、统一跨文件数值一致性

- 统一 AdamW 优化器显存计算：7B 模型的优化器状态应为 84GB（12 bytes/param），而非 56GB 或 28GB
- 统一符号体系：使用一致的 Psi 或 bytes 表示法
- 确保索引文件与子文件数据一致

### 三、更新过时 API

- `python -m torch.distributed.launch` 统一为 `torchrun`
- `torch.cuda.amp.autocast/GradScaler` 更新为 `torch.amp`
- MLflow `transition_model_version_stage()` 更新为 Alias API
- Feast `Feature` 类更新为 `Field` 类
- Evidently 导入路径统一

### 四、补充缺失的关键主题（新增文件）

- 00-training-fundamentals：梯度累积、评估指标
- 02-distributed-training：激活重计算（Activation Checkpointing）、Scaling Laws
- 其他领域按优先级选择性补充

### 五、修复文档结构问题

- 将 `13-adamw-optimizer.md` 加入索引表
- 精简索引文件与子文件的高度重复内容
- 修正 README 路径 B 阅读时间矛盾（4小时 vs 5小时总计）

## 技术栈

- 文件格式：Markdown (.md)
- 项目规范：遵循 Skill 规范结构（SKILL.md 主入口 + references/ 子目录 + 子文件夹分层）
- 版本管理：Git（当前在 `ai-infra` 分支）

## 实现方案

### 整体策略

采用 **分领域批量修复** 策略：将 87+ 个文件按 8 大领域分组，每个领域批量处理该领域内的所有修改（事实错误 + 数值一致性 + API 更新 + 结构修复），最后统一处理跨领域的新增内容。

### 关键决策

1. **修复优先级**：严重事实错误 > 数值一致性 > 过时 API > 缺失主题补充 > 结构优化
2. **索引文件精简策略**：保留索引文件的概要性质，删除与子文件高度重复的详细内容，改为简要概述 + 链接跳转
3. **新增文件控制**：仅补充最关键的缺失主题（激活重计算、梯度累积等），避免过度膨胀文档体量
4. **符号统一**：全局统一使用"bytes/param"直观表述而非 M/Psi 符号，降低理解门槛

### 修改范围与影响分析

按领域统计需修改的文件：

| 领域 | 需修改文件数 | 新增文件数 | 修改类型 |
| --- | --- | --- | --- |
| 00-training-fundamentals | 5 | 1 | 事实错误、时间矛盾、新增主题 |
| 01-gpu-hardware | 5 | 0 | 硬件规格错误、代码修复 |
| 02-distributed-training | 7 | 1 | 数值一致性、API 更新、新增主题 |
| 03-inference-serving | 0 | 0 | 跨文件不一致（较轻微，后续批次） |
| 04-mlops-llmops | 3 | 0 | 过时 API |
| 05-cluster-scheduling | 3 | 0 | PromQL 错误、表述修正 |
| 06-learning-roadmap | 1 | 0 | API 更新 |
| SKILL.md | 1 | 0 | 同步更新 |


## 实现注意事项

1. **数值准确性验证**：所有修改的数值计算应附带推导过程（如 7B × 12 bytes = 84GB），便于后续验证
2. **向后兼容**：不改变现有文件名和目录结构，新增文件采用递增编号
3. **最小化影响**：仅修改有确认问题的内容，不做无关重构
4. **保持风格一致**：新增内容遵循现有文件的类比风格（生活化比喻 + ASCII 图 + 代码示例）

## 架构设计

当前文件组织结构合理，无需调整架构。修改在现有结构内进行：

```
skills/ai-infra/
├── SKILL.md                              # [MODIFY] 更新核心知识领域描述同步新增子文件
├── references/
│   ├── 00-training-fundamentals.md       # [MODIFY] 无直接修改（索引在 README.md）
│   ├── 00-training-fundamentals/
│   │   ├── README.md                     # [MODIFY] 修正路径 B 时间矛盾、新增文件导航
│   │   ├── 02-neural-network-basics.md   # [MODIFY] 修正 LLaMA-7B FFN SwiGLU 参数描述
│   │   ├── 04-loss-function.md           # [MODIFY] 删除未证实的 GPT-4 PPL 推测
│   │   ├── 06-gradient-descent.md        # [MODIFY] 修正 CosineAnnealingLR + warmup 代码
│   │   ├── 07-mountain-valley-training.md # [MODIFY] 修正 A100 GPU 费用估算
│   │   ├── 10-transformer-architecture.md # [MODIFY] 修正 Softmax 计算数值
│   │   └── 13-gradient-accumulation.md   # [NEW] 梯度累积与评估指标专题
│   ├── 01-gpu-hardware.md                # [MODIFY] 修正 Register File 64KB→256KB、删除 B100
│   ├── 01-gpu-hardware/
│   │   ├── 02-architecture-evolution.md  # [MODIFY] 修正能效比对比（统一 dense/sparse 口径）
│   │   ├── 03-nvidia-architecture.md     # [MODIFY] 修正架构识别代码 (Turing/Ada)
│   │   ├── 06-tensor-core.md             # [MODIFY] 修正 Volta INT8 Tensor Core 标记
│   │   └── 08-hardware-selection.md      # [MODIFY] 修正消费级 GPU TFLOPS、TCO 分水岭
│   ├── 02-distributed-training.md        # [MODIFY] 修正优化器显存 56GB→84GB、统一符号、修正训练年限、更新 API
│   ├── 02-distributed-training/
│   │   ├── README.md                     # [MODIFY] 将 13-adamw-optimizer.md 加入索引
│   │   ├── 01-why-distributed.md         # [MODIFY] 修正单 A100 训练 GPT-3 时长估算
│   │   ├── 03-data-parallelism.md        # [MODIFY] 修正 DDP 框显存数值 28GB→84GB
│   │   ├── 05-pipeline-parallelism.md    # [MODIFY] 修正优化器显存数值
│   │   ├── 07-training-frameworks.md     # [MODIFY] 修正显存数值、更新 torch.distributed.launch
│   │   ├── 12-mixed-precision-training.md # [MODIFY] 修正 FP32 master weights 描述混淆
│   │   └── 14-activation-checkpointing.md # [NEW] 激活重计算（Activation Checkpointing）专题
│   ├── 04-mlops-llmops.md                # [MODIFY] 更新 MLflow Alias API、Feast Field 类
│   ├── 04-mlops-llmops/
│   │   ├── 04-model-registry.md          # [MODIFY] 更新 transition_model_version_stage
│   │   └── 07-model-monitoring.md        # [MODIFY] 统一 Evidently 导入路径
│   ├── 05-cluster-scheduling/
│   │   ├── 05-resource-isolation.md      # [MODIFY] 修正 Kueue 定位描述
│   │   ├── 07-cost-optimization.md       # [MODIFY] 修正 PromQL increase() 用法
│   │   └── 08-gpu-monitoring.md          # [MODIFY] 修正 PromQL 指标名
│   └── 06-learning-roadmap/
│       └── 08-interview-preparation.md   # [MODIFY] 更新 torch.cuda.amp → torch.amp
```

## Agent Extensions

### Skill

- **skill-creator**
- 用途：确保新增和修改的文件符合 Skill 规范格式，验证 SKILL.md 入口文件的规范性
- 预期结果：所有修改后的文件满足 Skill 规范要求

### SubAgent

- **code-explorer**
- 用途：在批量修改前，对每个领域的待修改文件进行精确定位，确认错误行号和上下文
- 预期结果：为每个修改任务提供准确的文件路径、行号和上下文