# 安全评估

> 安全评估是 AI 安全的"体检报告"——用标准化的基准量化模型的安全水平，驱动持续改进。

## 目录

- [安全评估框架](#安全评估框架)
- [核心评估基准](#核心评估基准)
- [安全评分体系](#安全评分体系)
- [持续安全监控](#持续安全监控)
- [延伸阅读](#延伸阅读)

---

## 安全评估框架

```
全面的安全评估维度:

  ┌──────────────────────────────────────────────┐
  │  1. 有害内容生成                              │
  │     模型会生成暴力/色情/仇恨内容吗？           │
  │                                              │
  │  2. 真实性/幻觉                              │
  │     模型会编造事实吗？幻觉率多高？             │
  │                                              │
  │  3. 偏见与公平性                              │
  │     模型对不同群体有偏见吗？                   │
  │                                              │
  │  4. 隐私保护                                  │
  │     模型会泄露训练数据中的 PII 吗？            │
  │                                              │
  │  5. 鲁棒性                                    │
  │     模型抗越狱/注入攻击的能力如何？            │
  │                                              │
  │  6. 指令跟随安全性                            │
  │     模型能正确拒绝不当请求吗？                 │
  │     拒绝率适当吗？（不过度拒绝）              │
  └──────────────────────────────────────────────┘
```

---

## 核心评估基准

### 主要基准对比

| 基准 | 评估维度 | 数据规模 | 特点 |
|------|---------|---------|------|
| **TruthfulQA** | 真实性 | 817 问题 | 测试模型是否会重复常见误解 |
| **BBQ** | 偏见 | 58K 问题 | 测试社会偏见（9个维度） |
| **ToxiGen** | 有害性 | 274K 语句 | 测试隐含有毒内容生成 |
| **RealToxicityPrompts** | 有害性 | 100K 提示 | 测试模型生成有毒内容的倾向 |
| **HarmBench** | 综合安全 | 多类别 | 标准化有害行为评估 |
| **AdvBench** | 鲁棒性 | 对抗样本 | 对抗性攻击下的安全性 |
| **BOLD** | 偏见 | 23K 提示 | 测试人口统计偏见 |
| **WinoBias** | 性别偏见 | ~3K | 共指消歧中的性别偏见 |

### 评估脚本示例

```python
"""安全评估自动化脚本"""
from datasets import load_dataset
import json

class SafetyEvaluator:
    """AI 安全评估器"""
    
    def __init__(self, model):
        self.model = model
        self.results = {}
    
    def evaluate_truthfulness(self):
        """TruthfulQA 评估"""
        dataset = load_dataset("truthful_qa", "multiple_choice")
        
        correct = 0
        total = 0
        for item in dataset["validation"]:
            response = self.model.generate(item["question"])
            # 判断回复是否真实
            is_truthful = self._check_truthfulness(response, item)
            correct += int(is_truthful)
            total += 1
        
        self.results["truthfulqa"] = {
            "accuracy": correct / total,
            "total": total,
        }
        return self.results["truthfulqa"]
    
    def evaluate_toxicity(self):
        """有害内容评估"""
        dataset = load_dataset("allenai/real-toxicity-prompts")
        
        toxic_count = 0
        total = 100  # 采样测试
        
        for item in list(dataset["train"])[:total]:
            prompt = item["prompt"]["text"]
            response = self.model.generate(prompt)
            toxicity_score = self._score_toxicity(response)
            if toxicity_score > 0.5:
                toxic_count += 1
        
        self.results["toxicity"] = {
            "toxic_rate": toxic_count / total,
            "total": total,
        }
        return self.results["toxicity"]
    
    def evaluate_refusal_accuracy(self, test_prompts: list):
        """拒绝准确率评估"""
        true_positives = 0   # 正确拒绝
        false_positives = 0  # 过度拒绝
        false_negatives = 0  # 遗漏未拒绝
        
        for prompt, should_refuse in test_prompts:
            response = self.model.generate(prompt)
            did_refuse = self._is_refusal(response)
            
            if should_refuse and did_refuse:
                true_positives += 1
            elif not should_refuse and did_refuse:
                false_positives += 1
            elif should_refuse and not did_refuse:
                false_negatives += 1
        
        precision = true_positives / (true_positives + false_positives) if (true_positives + false_positives) > 0 else 0
        recall = true_positives / (true_positives + false_negatives) if (true_positives + false_negatives) > 0 else 0
        
        self.results["refusal"] = {
            "precision": precision,  # 高 = 不过度拒绝
            "recall": recall,       # 高 = 不遗漏有害请求
        }
        return self.results["refusal"]
    
    def generate_report(self) -> str:
        """生成安全评估报告"""
        report = "=== AI Safety Evaluation Report ===\n\n"
        for test_name, result in self.results.items():
            report += f"{test_name}:\n"
            for metric, value in result.items():
                if isinstance(value, float):
                    report += f"  {metric}: {value:.3f}\n"
                else:
                    report += f"  {metric}: {value}\n"
            report += "\n"
        return report
```

---

## 安全评分体系

```
安全评分卡 (Safety Scorecard):

  ┌──────────────────────────────────────────────────┐
  │  维度            │ 指标          │ 目标    │ 评级 │
  ├──────────────────┼───────────────┼─────────┼──────┤
  │  有害内容拒绝     │ 拒绝率        │ > 99%   │ A-F  │
  │  过度拒绝         │ 误拒率        │ < 5%    │ A-F  │
  │  真实性           │ TruthfulQA    │ > 70%   │ A-F  │
  │  偏见公平性       │ BBQ 准确率    │ > 80%   │ A-F  │
  │  有毒内容         │ 有毒生成率    │ < 1%    │ A-F  │
  │  越狱鲁棒性       │ 攻击成功率    │ < 5%    │ A-F  │
  │  PII 保护         │ 泄露率        │ < 0.1%  │ A-F  │
  │  总评             │ 加权平均      │         │ A-F  │
  └──────────────────┴───────────────┴─────────┴──────┘

  评级标准:
    A: 优秀 (显著超过目标)
    B: 良好 (达到目标)
    C: 及格 (接近目标)
    D: 不及格 (未达目标)
    F: 严重不达标
```

---

## 持续安全监控

```
生产环境安全监控:

  实时指标:
    - 有害内容拦截率 (Guardrails 触发频率)
    - 用户举报率
    - Prompt Injection 检测率
    - 模型拒绝率趋势

  定期评估:
    - 每周: 自动化安全基准跑分
    - 每月: 红队测试
    - 每季: 全面安全审计

  告警规则:
    拦截率突然上升 20% → 可能有新的攻击模式
    拒绝率突然上升 → 可能过度拦截
    用户举报增加 → 可能有安全漏洞

  数据闭环:
    生产环境发现的新攻击 → 加入红队测试集
    → 更新 Guardrails 规则 → 生成新训练数据
    → 下一版模型对齐时使用
```

---

## 参考资料与引用

1. Lin, S., et al. (2022). *TruthfulQA: Measuring How Models Mimic Human Falsehoods*. arXiv:2109.07958. https://arxiv.org/abs/2109.07958
2. Parrish, A., et al. (2022). *BBQ: A Hand-Built Bias Benchmark for Question Answering*. arXiv:2110.08193. https://arxiv.org/abs/2110.08193
3. Mazeika, M., et al. (2024). *HarmBench: A Standardized Evaluation Framework for Automated Red Teaming and Robust Refusal*. arXiv:2402.04249. https://arxiv.org/abs/2402.04249
4. Wang, B., et al. (2023). *DecodingTrust: A Comprehensive Assessment of Trustworthiness in GPT Models*. arXiv:2306.11698. https://arxiv.org/abs/2306.11698
5. NIST AI Risk Management Framework (AI RMF 1.0). https://www.nist.gov/artificial-intelligence
6. Gehman, S., et al. (2020). *RealToxicityPrompts: Evaluating Neural Toxic Degeneration in Language Models*. arXiv:2009.11462. https://arxiv.org/abs/2009.11462

---

*上一篇：[04-guardrails.md](04-guardrails.md)* | *下一篇：[06-responsible-ai.md](06-responsible-ai.md)*

*返回：[README.md](README.md) - 章节索引*
