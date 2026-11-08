# 数据合规

> 用了不该用的数据训练模型，可能面临巨额罚款和声誉损失——数据合规是 AI 公司的生死线。

## 目录

- [版权问题](#版权问题)
- [隐私保护与 PII](#隐私保护与-pii)
- [法规合规](#法规合规)
- [数据许可证](#数据许可证)
- [合规实践清单](#合规实践清单)
- [延伸阅读](#延伸阅读)

---

## 版权问题

```
AI 训练数据的版权争议:

  核心问题: 用版权内容训练 AI 模型是否构成侵权？

  正在进行的法律案件:
    NYT vs OpenAI: 纽约时报起诉版权侵权
    Getty Images vs Stability AI: 图片版权侵权
    Authors Guild vs OpenAI: 作家权益

  不同立场:
    AI 公司: 训练是"合理使用" (Fair Use)
    版权方: 未经授权使用版权内容
    各国法规: 仍在演进中

  最佳实践:
    ✓ 使用明确许可的开源数据集
    ✓ 记录所有数据来源和许可证
    ✓ 实现 opt-out 机制 (robots.txt 尊重)
    ✓ 避免模型逐字复述版权内容
    ✓ 法律团队参与数据采集决策
```

---

## 隐私保护与 PII

### PII 检测与脱敏

```python
"""PII 检测与脱敏工具"""
import re
from typing import List, Tuple

class PIIDetector:
    """个人身份信息检测器"""
    
    PATTERNS = {
        "email": r'\b[\w.+-]+@[\w-]+\.[\w.-]+\b',
        "phone_cn": r'\b1[3-9]\d{9}\b',
        "phone_us": r'\b\d{3}[-.]?\d{3}[-.]?\d{4}\b',
        "id_card_cn": r'\b\d{17}[\dXx]\b',
        "ssn_us": r'\b\d{3}-\d{2}-\d{4}\b',
        "credit_card": r'\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b',
        "ip_address": r'\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b',
    }
    
    def detect(self, text: str) -> List[dict]:
        """检测文本中的 PII"""
        findings = []
        for pii_type, pattern in self.PATTERNS.items():
            for match in re.finditer(pattern, text):
                findings.append({
                    "type": pii_type,
                    "value": match.group(),
                    "start": match.start(),
                    "end": match.end(),
                })
        return findings
    
    def redact(self, text: str) -> str:
        """脱敏: 替换 PII 为占位符"""
        for pii_type, pattern in self.PATTERNS.items():
            placeholder = f"[{pii_type.upper()}]"
            text = re.sub(pattern, placeholder, text)
        return text

# 使用
detector = PIIDetector()
text = "Contact John at john@email.com or 13812345678"
print(detector.detect(text))
# [{"type": "email", "value": "john@email.com", ...},
#  {"type": "phone_cn", "value": "13812345678", ...}]

print(detector.redact(text))
# "Contact John at [EMAIL] or [PHONE_CN]"
```

---

## 法规合规

| 法规 | 地区 | 关键要求 | 对 AI 训练的影响 |
|------|------|---------|-----------------|
| **GDPR** | 欧盟 | 数据最小化、被遗忘权、同意 | 训练数据需合法基础 |
| **CCPA/CPRA** | 美国加州 | 消费者数据权利、opt-out | 需提供数据删除选项 |
| **个人信息保护法** | 中国 | 知情同意、最小必要、跨境传输 | 数据出境需安全评估 |
| **AI Act** | 欧盟 | 训练数据记录、版权合规 | 需记录数据来源 |
| **Copyright Act** | 多国 | 版权保护、合理使用 | 训练数据版权合规 |

```
GDPR 对 AI 训练的关键要求:

  1. 合法基础 (Legal Basis):
     同意 / 合法利益 / 合同必需
     → AI 训练通常基于"合法利益"

  2. 数据最小化:
     只收集必要的数据
     → 不要收集与训练目标无关的数据

  3. 被遗忘权 (Right to Erasure):
     用户请求删除其数据
     → 难题: 如何从已训练的模型中"删除"数据?
     → 解决: 记录数据来源，下次训练时排除

  4. 数据保护影响评估 (DPIA):
     大规模数据处理前需评估风险
     → AI 训练通常需要 DPIA
```

---

## 数据许可证

| 许可证 | 商用 | 修改 | 分享 | 常见数据集 |
|--------|------|------|------|-----------|
| **CC BY 4.0** | ✓ | ✓ | ✓(注明出处) | Wikipedia |
| **CC BY-SA 4.0** | ✓ | ✓ | ✓(相同许可) | StackOverflow |
| **CC BY-NC 4.0** | ✗ | ✓ | ✓ | 部分学术数据 |
| **Apache 2.0** | ✓ | ✓ | ✓ | RedPajama |
| **MIT** | ✓ | ✓ | ✓ | 多种代码数据 |
| **Llama License** | 有限制 | ✓ | ✓(条件) | Llama 模型/数据 |
| **ODC-By** | ✓ | ✓ | ✓(注明) | Common Crawl |

---

## 合规实践清单

```
AI 数据合规实践清单:

  数据采集阶段:
    □ 记录所有数据来源和许可证
    □ 遵守 robots.txt 和网站 ToS
    □ 实现 opt-out 机制
    □ 进行数据保护影响评估 (DPIA)

  数据处理阶段:
    □ PII 检测和脱敏
    □ 版权内容过滤
    □ 有害/违法内容过滤
    □ 数据血缘记录

  存储阶段:
    □ 数据加密（静态和传输中）
    □ 访问控制（RBAC）
    □ 数据保留策略
    □ 跨境传输合规

  使用阶段:
    □ 训练日志记录数据版本
    □ 模型不逐字复述训练数据
    □ 定期合规审计

  删除/更新:
    □ 数据删除请求处理流程
    □ 定期数据清理
    □ 更新合规文档
```

---

## 参考资料与引用

1. GDPR (General Data Protection Regulation) - Official Text. https://gdpr.eu/
2. CCPA (California Consumer Privacy Act) - Official Resources. https://oag.ca.gov/privacy/ccpa
3. Creative Commons License Chooser. https://creativecommons.org/choose/
4. Congressional Research Service - AI and Copyright. https://crsreports.congress.gov/
5. Microsoft Presidio - PII Detection and Anonymization. https://github.com/microsoft/presidio
6. Henderson, P., et al. (2023). *Foundation Models and Fair Use*. arXiv:2303.15715. https://arxiv.org/abs/2303.15715
7. Min, S., et al. (2023). *SILO Language Models: Isolating Legal Risk In a Nonparametric Datastore*. arXiv:2308.04430. https://arxiv.org/abs/2308.04430

---

*上一篇：[05-data-versioning.md](05-data-versioning.md)*

*返回：[README.md](README.md) - 章节索引*
