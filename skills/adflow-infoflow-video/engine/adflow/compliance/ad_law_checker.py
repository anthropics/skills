"""
广告法合规审查
- 敏感词检测（绝对化用语、医疗承诺、金融承诺等）
- 平台特定规则
- 返回检测结果 + 违规详情
"""

import re
from pathlib import Path
from dataclasses import dataclass, field


@dataclass
class ComplianceResult:
    """合规审查结果"""
    passed: bool = True
    violations: list[dict] = field(default_factory=list)   # [{word, category, position}]
    warnings: list[str] = field(default_factory=list)


class AdLawChecker:
    """广告法敏感词检测器"""

    # 内置敏感词分类
    _builtin_words: dict[str, list[str]] = {
        "绝对化用语": [
            "最好", "第一", "唯一", "独家", "首选", "顶级", "极致",
            "绝对", "100%", "百分百", "万能", "无敌", "全网第一",
            "国家级", "世界级", "最高级", "最佳", "最优", "史上最",
            "最便宜", "最先进", "最新科技", "独一无二",
        ],
        "医疗承诺": [
            "治愈", "根治", "药到病除", "永不复发", "无副作用",
            "包治百病", "一疗程见效", "彻底根除", "临床验证",
            "有效率", "治愈率",
        ],
        "金融承诺": [
            "保本", "保收益", "无风险", "稳赚", "年化收益.*%",
            "只赚不赔", "本金保障", "收益.*%以上",
        ],
        "诱导点击": [
            "点击领取", "免费领取", "不领就亏了", "限时免费",
            "点击就送",
        ],
        "虚假紧迫": [
            "最后一天", "最后.*小时", "仅剩.*件", "即将涨价",
            "马上结束", "错过等一年", "手慢无",
        ],
        "贬低竞品": [
            "垃圾", "骗人", "千万别买", "智商税",
        ],
    }

    def __init__(self):
        self._sensitive_words: dict[str, list[str]] = dict(self._builtin_words)
        self._load_custom_words()

    def check(self, text: str, platform: str = "ocean_engine") -> ComplianceResult:
        """
        检查文本是否合规
        返回 ComplianceResult
        """
        result = ComplianceResult()

        if not text:
            return result

        for category, words in self._sensitive_words.items():
            for word in words:
                # 使用正则匹配（部分词含正则表达式如 .*%）
                for match in re.finditer(word, text, re.IGNORECASE):
                    result.violations.append({
                        "word": match.group(),
                        "category": category,
                        "position": match.start(),
                    })

        # 平台特定规则
        platform_warnings = self._check_platform_rules(text, platform)
        result.warnings.extend(platform_warnings)

        result.passed = len(result.violations) == 0
        return result

    def check_multiple(self, texts: dict[str, str], platform: str = "ocean_engine") -> ComplianceResult:
        """
        批量检查多段文本
        texts: {标识: 文本内容, ...}
        """
        combined = ComplianceResult()
        for label, text in texts.items():
            r = self.check(text, platform)
            if not r.passed:
                for v in r.violations:
                    v["source"] = label
                combined.violations.extend(r.violations)
            combined.warnings.extend(r.warnings)
        combined.passed = len(combined.violations) == 0
        return combined

    def has_violations(self, text: str) -> bool:
        """快速检查：是否有违规"""
        return not self.check(text).passed

    def get_violation_summary(self, result: ComplianceResult) -> str:
        """违规摘要 → 可读字符串"""
        if result.passed:
            return "合规通过 ✓"
        lines = ["发现违规:"]
        for v in result.violations:
            lines.append(f"  - [{v['category']}] [{v['word']}]")
        for w in result.warnings:
            lines.append(f"  ⚠ {w}")
        return "\n".join(lines)

    def _check_platform_rules(self, text: str, platform: str) -> list[str]:
        """平台特定规则检查"""
        warnings = []

        if platform == "ocean_engine":
            # 信息流平台品类限制（示例）
            if "医疗" in text or "药品" in text:
                warnings.append("信息流平台医疗类需白名单资质")
            if "金融" in text or "贷款" in text:
                warnings.append("金融类需特殊资质审核")
            if "彩票" in text:
                warnings.append("信息流平台禁止彩票类广告")

        return warnings

    def _load_custom_words(self) -> None:
        """加载自定义敏感词库"""
        word_file = Path(__file__).parent / "sensitive_words.txt"
        if not word_file.exists():
            return

        current_category = None
        with open(word_file, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("[") and line.endswith("]"):
                    current_category = line[1:-1]
                    if current_category not in self._sensitive_words:
                        self._sensitive_words[current_category] = []
                elif current_category:
                    self._sensitive_words[current_category].append(line)
