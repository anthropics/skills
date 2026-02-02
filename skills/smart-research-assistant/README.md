# Smart Research Assistant - 使用指南

## 技能概述

这是一个综合研究技能，帮助进行多源调研、评估信息可信度，并生成结构化的markdown报告。

## 主要功能

### 🔍 信息评估框架
- **SIFT方法**：快速信息验证（停止、调查、寻找、追溯）
- **WWWDOT框架**：详细来源分析（谁、为何、何时、是否有用、组织、待办）
- **CAPES框架**：系统化评估（背景、行动、产出、评估、标准）
- **横向阅读**：专业事实核查技术

### 📊 多源数据整合
- 学术来源：期刊论文、会议论文、研究报告
- 专业数据：行业报告、政府数据、公司财报
- 网络资源：新闻网站、博客、社交媒体
- 可视化：自动生成图表和数据可视化

### 📋 结构化报告生成
- 研究背景和上下文分析
- 数据分析和发现展示
- 可视化图表和统计表格
- 关键洞察和建议

## 使用方法

### 1. 基础研究
```bash
# 评估单个来源
python scripts/source_verifier.py "https://example.com/article"

# 分析内容可信度
python scripts/source_verifier.py "https://example.com" content.txt "News Site"
```

### 2. 批量源验证
```bash
# 验证多个来源
echo "https://reuters.com/article\nhttps://cnn.com/article" > sources.txt
python scripts/source_verifier.py $(cat sources.txt)
```

### 3. 文献引用格式化
```json
{
  "sources": [
    {
      "type": "journal_article",
      "author": "Smith, J.",
      "year": "2023",
      "title": "Research Methodology in Digital Age",
      "journal": "Journal of Research Methods",
      "volume": "15",
      "issue": "2",
      "pages": "123-145",
      "doi": "10.1234/research.2023.1234"
    }
  ]
}
```

### 4. 生成引用
```bash
# APA格式
python scripts/citation_formatter.py sources.json --style apa

# MLA格式
python scripts/citation_formatter.py sources.json --style mla --output bibliography.md
```

### 5. 数据可视化
```json
{
  "categories": ["源A", "源B", "源C"],
  "values": [85, 72, 93],
  "x_label": "信息来源",
  "y_label": "可信度得分"
}
```

### 6. 生成图表
```bash
# 柱状图
python scripts/data_visualizer.py data.json --type bar --title "来源可信度分析"

# 研究摘要图
python scripts/data_visualizer.py research_data.json --research-summary
```

## 工作流程

### 阶段1：规划与范围定义
1. 明确研究目标
2. 定义关键问题
3. 设定成功标准
4. 识别相关利益相关者

### 阶段2：信息收集
1. 多源数据采集
2. 来源多样性检查
3. 质量初步筛选
4. 数据组织整理

### 阶段3：来源评估
1. 应用SIFT快速验证
2. 使用WWWDOT详细分析
3. CAPES系统化评估
4. 横向阅读交叉验证

### 阶段4：分析与综合
1. 跨源验证
2. 模式识别
3. 趋势分析
4. 差距分析

### 阶段5：报告生成
1. 背景上下文描述
2. 分析发现展示
3. 数据可视化元素
4. 关键洞察建议

## 报告模板

### 学术研究报告
- 执行摘要 + 背景分析 + 方法论 + 发现 + 讨论 + 结论 + 参考文献

### 市场调研报告
- 研究概述 + 市场分析 + 竞品对比 + 机会识别 + 建议方案

### 事实核查报告
- 声明验证 + 来源评估 + 证据分析 + 结论 + 可信度评级

## 质量保证

### 自动化检查
- 来源可信度评分
- 内容偏见检测
- 引用完整性验证
- 数据准确性审核

### 人工审核要点
- 逻辑一致性检查
- 证据充分性评估
- 结论合理性判断
- 建议可行性分析

## 最佳实践

### 信息源选择
1. 优先学术同行评议来源
2. 检查作者专业资质
3. 验证出版机构声誉
4. 注意出版时效性

### 分析技巧
1. 使用多种评估框架
2. 进行横向阅读验证
3. 保持批判性思维
4. 记录分析过程

### 报告撰写
1. 结构清晰，逻辑严密
2. 数据支撑，证据确凿
3. 观点平衡，偏见最少
4. 引用规范，格式统一

## 注意事项

### 局限性说明
- 工具基于启发式算法
- 需要人工判断辅助
- 文化语言可能影响
- 快速变化的信息源

### 持续改进
- 收集用户反馈
- 更新评估标准
- 扩展数据源覆盖
- 优化算法准确性

---

**Smart Research Assistant** 让您的网络研究更加专业、高效、可信！