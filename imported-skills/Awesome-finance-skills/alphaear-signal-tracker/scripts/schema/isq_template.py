"""
ISQ (Investment Signal Quality) 评估框架 Template

统一定义 ISQ 的各个维度、评分标准、和使用方法。
支持默认 template 和自定义 template。
"""

from typing import Dict, List, Any, Optional
from pydantic import BaseModel, Field
from enum import Enum
from pathlib import Path
import json


class ISQDimension(str, Enum):
    """ISQ 评估维度"""
    SENTIMENT = "sentiment"              # 情绪/走势方向
    CONFIDENCE = "confidence"            # 确定性/可信度
    INTENSITY = "intensity"              # 强度/影响量级
    EXPECTATION_GAP = "expectation_gap"  # 预期差/市场认知差
    TIMELINESS = "timeliness"            # 时效性/窗口紧迫度
    TRANSMISSION = "transmission"        # 逻辑传导清晰度


class ISQDimensionSpec(BaseModel):
    """ISQ 单个维度的定义规范"""
    name: str = Field(..., description="维度名称")
    key: str = Field(..., description="维度键名")
    description: str = Field(..., description="维度描述")
    range_type: str = Field(default="0-1", description="取值范围 (0-1 或 1-5 等)")
    scale_factor: float = Field(default=1.0, description="显示时的缩放因子")
    examples: Dict[str, str] = Field(default_factory=dict, description="不同分值的示例解释")
    visualization_color: Optional[str] = Field(default=None, description="可视化颜色")


class ISQTemplate(BaseModel):
    """ISQ 评估框架 Template"""
    template_id: str = Field(..., description="模板 ID")
    template_name: str = Field(..., description="模板名称")
    description: str = Field(..., description="模板描述")
    
    # 核心维度定义
    dimensions: Dict[str, ISQDimensionSpec] = Field(..., description="维度定义字典")
    
    # 评分指导
    scoring_guide: str = Field(..., description="评分指导说明")
    
    # 应用场景
    applicable_scenarios: List[str] = Field(default_factory=list, description="适用场景")
    
    # 聚合算法
    aggregation_method: str = Field(default="weighted_average", description="聚合方法 (weighted_average, product 等)")
    dimension_weights: Dict[str, float] = Field(default_factory=dict, description="维度权重")


class ISQScore(BaseModel):
    """单个信号的 ISQ 评分结果"""
    signal_id: str = Field(..., description="信号 ID")
    template_id: str = Field(..., description="使用的模板 ID")
    
    # 各维度评分
    scores: Dict[str, float] = Field(..., description="各维度评分")
    
    # 总分
    overall_score: float = Field(..., description="综合评分")
    
    # 评分理由
    rationale: Dict[str, str] = Field(default_factory=dict, description="各维度评分理由")
    
    # 时间戳
    timestamp: str = Field(..., description="评分时间")


# =====================================================
# 默认 Template
# =====================================================

DEFAULT_ISQ_TEMPLATE = ISQTemplate(
    template_id="default_isq_v1",
    template_name="标准投资信号质量评估框架 (ISQ v1.0)",
    description="AlphaEar 默认的 ISQ 评估框架，用于标准化评估投资信号的质量维度",
    
    dimensions={
        "sentiment": ISQDimensionSpec(
            name="情绪/走势",
            key="sentiment",
            description="基础情绪偏向和市场走势判断",
            range_type="-1.0 到 1.0",
            scale_factor=1.0,
            examples={
                "-1.0": "极度悲观/极度看空",
                "-0.5": "明显看空",
                "0.0": "中性/没有明确方向",
                "0.5": "明显看多",
                "1.0": "极度乐观/极度看多"
            },
            visualization_color="#ef4444"  # 红色表示负面，绿色表示正面
        ),
        
        "confidence": ISQDimensionSpec(
            name="确定性",
            key="confidence",
            description="信号的可信度和确定性程度",
            range_type="0.0 到 1.0",
            scale_factor=1.0,
            examples={
                "0.0-0.3": "信息来源不可靠/传言多/逻辑推导牵强",
                "0.3-0.6": "信息相对可靠/有一定逻辑/但仍有不确定性",
                "0.6-0.8": "信息来源权威/逻辑清晰/高度可信",
                "0.8-1.0": "官方确认/数据明确/完全确定"
            },
            visualization_color="#3b82f6"  # 蓝色
        ),
        
        "intensity": ISQDimensionSpec(
            name="强度/影响量级",
            key="intensity",
            description="信号对相关板块/个股的潜在影响程度",
            range_type="1 到 5",
            scale_factor=20.0,  # 用于雷达图缩放 (5 -> 100)
            examples={
                "1": "影响微弱，可能被市场忽略",
                "2": "小幅影响，短期可能有波动",
                "3": "中等影响，值得重点关注",
                "4": "强烈影响，可能成为市场焦点",
                "5": "极强影响，市场预期明显变化"
            },
            visualization_color="#f97316"  # 橙色
        ),
        
        "expectation_gap": ISQDimensionSpec(
            name="预期差",
            key="expectation_gap",
            description="市场预期与现实之间的差距",
            range_type="0.0 到 1.0",
            scale_factor=1.0,
            examples={
                "0.0-0.2": "市场充分认知，预期差小",
                "0.2-0.5": "市场部分认知，存在一定预期差",
                "0.5-0.8": "市场认知不足，预期差较大，存在博弈空间",
                "0.8-1.0": "市场严重低估/高估，巨大预期差"
            },
            visualization_color="#22c55e"  # 绿色
        ),
        
        "timeliness": ISQDimensionSpec(
            name="时效性",
            key="timeliness",
            description="信号的时间窗口紧迫度",
            range_type="0.0 到 1.0",
            scale_factor=1.0,
            examples={
                "0.0-0.2": "长期信号，反应窗口 > 3 月",
                "0.2-0.5": "中期信号，反应窗口 1-3 月",
                "0.5-0.8": "短期信号，反应窗口 1 周 - 1 月",
                "0.8-1.0": "超短期信号，反应窗口 < 1 周（需立即行动）"
            },
            visualization_color="#a855f7"  # 紫色
        ),
    },
    
    scoring_guide="""
    ### ISQ 评分指导 (Investment Signal Quality)
    
    ISQ 框架用于多维度评估投资信号的质量。每个信号由 5 个维度组成：
    
    1. **情绪 (Sentiment)**: -1.0 到 1.0，表示看空(-)/中性(0)/看多(+)
    2. **确定性 (Confidence)**: 0.0 到 1.0，数值越高越确定
    3. **强度 (Intensity)**: 1 到 5，数值越高影响越大
    4. **预期差 (Expectation Gap)**: 0.0 到 1.0，市场预期与现实的差距
    5. **时效性 (Timeliness)**: 0.0 到 1.0，反应窗口的紧迫程度
    
    ### 综合评分算法
    
    综合评分 = 确定性 × 0.35 + 强度/5 × 0.30 + 预期差 × 0.20 + 时效性 × 0.15
    
    范围: 0.0 到 1.0
    - 0.0-0.3: 信号质量较差，不建议跟进
    - 0.3-0.6: 信号质量一般，可作参考
    - 0.6-0.8: 信号质量良好，值得跟进
    - 0.8-1.0: 信号质量优异，强烈推荐
    
    ### 评分时的注意事项
    
    - **不要混淆方向和强度**：情绪可以是看空，但确定性和强度仍可能很高
    - **预期差往往是 Alpha 来源**：高预期差 + 高确定性 = 最佳博弈机会
    - **考虑时间成本**：长期信号需要更高的确定性才值得跟进
    - **数据为王**：所有评分必须有具体数据支撑
    """,
    
    applicable_scenarios=[
        "上市公司基本面变化分析",
        "产业政策与监管事件评估",
        "地缘政治与宏观经济影响",
        "技术进步与产业升级",
        "突发事件与应急响应"
    ],
    
    aggregation_method="weighted_average",
    dimension_weights={
        "confidence": 0.35,
        "intensity": 0.30,
        "expectation_gap": 0.20,
        "timeliness": 0.15
    }
)


# =====================================================
# ISQ Template 管理系统
# =====================================================

class ISQTemplateManager:
    """ISQ Template 管理器"""
    
    def __init__(self):
        self.templates: Dict[str, ISQTemplate] = {
            DEFAULT_ISQ_TEMPLATE.template_id: DEFAULT_ISQ_TEMPLATE
        }
    
    def register_template(self, template: ISQTemplate) -> None:
        """注册新的 template"""
        self.templates[template.template_id] = template

    def register_template_dict(self, template_dict: Dict[str, Any]) -> ISQTemplate:
        """从 dict 注册模板，返回实例。"""
        tpl = ISQTemplate(**template_dict)
        self.register_template(tpl)
        return tpl
    
    def get_template(self, template_id: str) -> ISQTemplate:
        """获取指定 template"""
        if template_id not in self.templates:
            return DEFAULT_ISQ_TEMPLATE
        return self.templates[template_id]
    
    def list_templates(self) -> List[Dict[str, str]]:
        """列出所有可用 template"""
        return [
            {
                "id": t.template_id,
                "name": t.template_name,
                "description": t.description,
                "dimensions": list(t.dimensions.keys())
            }
            for t in self.templates.values()
        ]
    
    def get_dimension(self, template_id: str, dimension_key: str) -> ISQDimensionSpec:
        """获取指定 template 的某个维度定义"""
        template = self.get_template(template_id)
        return template.dimensions.get(dimension_key)
    
    def get_scoring_prompt(self, template_id: str) -> str:
        """获取用于 LLM 的评分 prompt"""
        template = self.get_template(template_id)
        
        dimensions_desc = "\n".join([
            f"- **{d.name} ({d.key})**\n"
            f"  范围: {d.range_type}\n"
            f"  说明: {d.description}\n"
            f"  示例: {', '.join(f'{k}={v}' for k, v in list(d.examples.items())[:3])}"
            for d in template.dimensions.values()
        ])
        
        return f"""
### ISQ 评估指导 ({template.template_name})

使用以下 {len(template.dimensions)} 个维度评估信号质量：

{dimensions_desc}

### 评分标准
{template.scoring_guide}

### 输出格式 (JSON)
请输出以下 JSON 格式的评分结果：
{{
  "sentiment": <float>,
  "confidence": <float>,
  "intensity": <int>,
  "expectation_gap": <float>,
  "timeliness": <float>,
  "rationale": {{
    "sentiment": "评分理由",
    "confidence": "评分理由",
    "intensity": "评分理由",
    "expectation_gap": "评分理由",
    "timeliness": "评分理由"
  }}
}}
"""


# 全局 template 管理器实例
isq_template_manager = ISQTemplateManager()


# =====================================================
# 配置加载
# =====================================================

def load_templates_from_config(config_path: Optional[str] = None) -> None:
    """从配置目录加载所有 JSON 模板文件，未找到则跳过，不影响默认模板。
    支持单个 JSON 文件或目录（目录下的所有 .json 文件）。
    """
    if config_path:
        path = Path(config_path)
    else:
        # 默认目录：config/isq_templates/
        # __file__ = src/schema/isq_template.py
        # parent = src/schema, parent.parent = src, parent.parent.parent = 项目根目录
        path = Path(__file__).resolve().parent.parent.parent / "config"
    
    if not path.exists():
        return
    
    # 如果是目录，扫描所有 .json 文件
    if path.is_dir():
        json_files = list(path.glob("*.json"))
    else:
        json_files = [path]
    
    for json_file in json_files:
        try:
            data = json.loads(json_file.read_text(encoding="utf-8"))
            
            # 如果是单个模板对象，转为列表
            if isinstance(data, dict):
                templates = [data]
            elif isinstance(data, list):
                templates = data
            else:
                continue
            
            # 注册所有模板
            for tpl_dict in templates:
                if not isinstance(tpl_dict, dict):
                    continue
                try:
                    isq_template_manager.register_template_dict(tpl_dict)
                except Exception:
                    # 忽略单个模板的加载错误，继续其他模板
                    continue
        except Exception:
            # JSON 解析失败，跳过该文件
            continue


# 在模块加载时自动尝试加载配置模板
load_templates_from_config()


# =====================================================
# 便利函数
# =====================================================

def get_isq_template(template_id: str = "default_isq_v1") -> ISQTemplate:
    """获取 ISQ template"""
    return isq_template_manager.get_template(template_id)


def get_isq_scoring_prompt(template_id: str = "default_isq_v1") -> str:
    """获取用于 LLM 的 ISQ 评分 prompt"""
    return isq_template_manager.get_scoring_prompt(template_id)


def calculate_isq_overall_score(scores: Dict[str, float], template_id: str = "default_isq_v1") -> float:
    """计算 ISQ 综合评分"""
    template = get_isq_template(template_id)
    
    overall = 0.0
    for dim_key, weight in template.dimension_weights.items():
        if dim_key in scores:
            score = scores[dim_key]
            # 处理强度维度的特殊缩放 (1-5 -> 0-1)
            if dim_key == "intensity":
                score = score / 5.0
            overall += score * weight
    
    return min(1.0, max(0.0, overall))  # 限制在 0-1 之间
