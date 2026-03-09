# 负责任 AI

> 技术能力需要伦理框架来引导——负责任 AI 不仅是技术问题，更是组织、法律和社会问题。

## 目录

- [负责任 AI 框架](#负责任-ai-框架)
- [偏见检测与缓解](#偏见检测与缓解)
- [可解释性与透明度](#可解释性与透明度)
- [法规合规](#法规合规)
- [组织实践](#组织实践)
- [延伸阅读](#延伸阅读)

---

## 负责任 AI 框架

```
负责任 AI 的核心原则:

  1. 公平性 (Fairness)
     模型不应对不同群体产生歧视
     检测和缓解训练数据与模型中的偏见

  2. 透明性 (Transparency)
     用户知道在和 AI 交互
     AI 的决策过程可解释
     公开模型能力与局限

  3. 隐私 (Privacy)
     保护训练数据中的个人信息
     不在推理时泄露 PII
     遵守数据保护法规

  4. 安全性 (Safety)
     模型不产生有害输出
     系统性的安全测试和监控
     故障时有安全降级机制

  5. 问责性 (Accountability)
     明确的责任归属
     完整的审计日志
     有效的申诉和纠错机制

  6. 可靠性 (Reliability)
     输出一致性和可预测性
     承认不确定性和局限
     持续监控和改进
```

---

## 偏见检测与缓解

### 偏见来源

```
AI 偏见的来源链:

  训练数据偏见:
    互联网文本本身包含社会偏见
    数据收集过程可能偏向特定群体
    标注员的个人偏见

  模型偏见:
    模型放大数据中的偏见
    特定架构可能对某些模式更敏感

  部署偏见:
    应用场景的选择偏差
    用户群体的代表性不足
    反馈循环加强偏见
```

### 偏见检测方法

```python
"""偏见检测示例"""

def detect_gender_bias(model, occupation_prompts: dict):
    """检测职业性别偏见"""
    results = {}
    
    for occupation, templates in occupation_prompts.items():
        male_prob = 0
        female_prob = 0
        
        for template in templates:
            # 例: "The {occupation} finished their work. They..."
            response = model.generate(template.format(occupation=occupation))
            
            # 分析代词使用
            he_count = response.lower().count(" he ")
            she_count = response.lower().count(" she ")
            
            male_prob += he_count
            female_prob += she_count
        
        total = male_prob + female_prob
        if total > 0:
            results[occupation] = {
                "male_ratio": male_prob / total,
                "female_ratio": female_prob / total,
                "bias_score": abs(male_prob - female_prob) / total,
            }
    
    return results

# 偏见缓解策略:
# 1. 数据层: 平衡训练数据的群体代表性
# 2. 训练层: 使用去偏见的对齐方法
# 3. 推理层: 后处理偏见校正
# 4. 评估层: 定期偏见基准测试
```

---

## 可解释性与透明度

```
AI 可解释性层次:

  Model Card (模型卡片):
    描述模型能力、训练数据、评估结果、局限性
    Meta Llama 3 Model Card 是优秀范例
    每个公开模型都应有 Model Card

  输出解释:
    置信度分数: 模型对输出的信心程度
    引用来源: RAG 场景中标注信息来源
    不确定性表达: "我不确定" vs 编造答案

  决策审计:
    记录关键决策的输入/输出
    支持事后审查
    保留足够长的审计日志
```

---

## 法规合规

### 主要法规

| 法规 | 地区 | 要求 | 影响 |
|------|------|------|------|
| **EU AI Act** | 欧盟 | 风险分级、透明性、人类监督 | 高风险 AI 需认证 |
| **GDPR** | 欧盟 | 数据保护、被遗忘权 | 训练数据合规 |
| **Executive Order on AI** | 美国 | 安全测试、标准制定 | 联邦政府使用 |
| **网络安全法/个人信息保护法** | 中国 | 数据安全、个人信息保护 | 模型备案 |
| **C-27 (AIDA)** | 加拿大 | AI 系统责任 | 高影响系统 |

### EU AI Act 关键要求

```
EU AI Act 对高风险 AI 的要求:

  1. 风险管理系统
     建立并维护风险管理流程
     定期更新风险评估

  2. 数据治理
     训练数据的质量、相关性、代表性
     偏见检测和缓解措施

  3. 技术文档
     系统描述、设计规范、测试方法
     性能指标和局限性

  4. 透明性
     用户知情权（在和 AI 交互）
     输出可追溯性

  5. 人类监督
     人类可以理解和干预 AI 决策
     override 机制

  6. 准确性、鲁棒性、安全性
     持续监控和改进
     对抗性鲁棒性

  合规建议:
    ✓ 建立 AI 治理委员会
    ✓ 实施 Model Card 制度
    ✓ 定期安全评估和审计
    ✓ 建立用户反馈和申诉渠道
    ✓ 保留完整的训练和部署文档
```

---

## 组织实践

```
负责任 AI 组织实践:

  1. AI 伦理委员会
     跨职能团队: 工程、法律、产品、伦理
     审查高风险 AI 应用
     制定和更新 AI 政策

  2. AI 安全团队
     红队测试
     安全评估和监控
     事件响应

  3. 文档和流程
     Model Card: 每个模型的能力和局限
     AI Impact Assessment: 上线前的影响评估
     Incident Response Plan: 安全事件处理流程

  4. 培训和文化
     全员 AI 伦理培训
     开发者安全编码培训
     建立负责任 AI 的文化

  5. 持续改进
     定期审计和评估
     用户反馈驱动改进
     跟踪法规变化和行业最佳实践
```

---

## 延伸阅读

- [EU AI Act](https://eur-lex.europa.eu/eli/reg/2024/1689/oj)
- [NIST AI Risk Management Framework](https://www.nist.gov/artificial-intelligence)
- [Google AI Principles](https://ai.google/responsibility/principles/)
- [Microsoft Responsible AI](https://www.microsoft.com/en-us/ai/responsible-ai)
- [Model Cards for Model Reporting](https://arxiv.org/abs/1810.03993)
- [Datasheets for Datasets](https://arxiv.org/abs/1803.09010)

---

*上一篇：[05-safety-evaluation.md](05-safety-evaluation.md)*

*返回：[README.md](README.md) - 章节索引*
