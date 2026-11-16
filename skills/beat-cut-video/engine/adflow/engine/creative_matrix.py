# -*- coding: utf-8 -*-
"""
创意发散矩阵 — 笛卡尔积(卖点×人群) + 加权选择 + 降权历史

替代随机文本清单，改为结构化角度格子:
  每个格子 = (卖点, 人群, 场景, 钩子方向)
  选择 = 加权随机（未用过优先，用过的指数衰减）
"""
import logging

logger = logging.getLogger("adflow.matrix")

# 品类→人群扩展
CATEGORY_AUDIENCES = {
    "坚果": ["便秘人群", "控糖人群", "办公室白领", "健身人群", "宝妈", "送礼", "学生党"],
    "零食": ["办公室白领", "学生党", "追剧党", "健身人群", "宝妈", "送礼", "控糖族"],
    "护肤": ["敏感肌", "油痘肌", "干皮", "抗老需求", "学生党", "职场女性", "宝妈"],
    "美妆": ["学生党", "职场女性", "约会党", "微胖人群", "化妆新手"],
    "数码": ["学生党", "职场白领", "游戏玩家", "户外爱好者", "极客"],
    "服装": ["通勤族", "学生党", "辣妹风", "极简风", "微胖人群", "孕妇"],
    "家居": ["新家装修", "租房党", "宝妈", "极简主义", "懒人"],
    "母婴": ["孕妈", "新手妈妈", "二胎家庭", "送礼人群"],
    "保健": ["中老年", "熬夜党", "健身人群", "病后恢复", "白领"],
    "食品": ["办公室白领", "学生党", "家庭主妇", "健身人群", "老年人", "送礼"],
}


class CreativeMatrix:
    """创意发散矩阵 — 笛卡尔积生成 + 加权选择"""

    def __init__(self, product_name: str = "", category: str = ""):
        self.product_name = product_name
        self.category = category
        self.angles: list[dict] = []

    def generate(self, selling_points: list[str],
                 extra_audiences: list[str] | None = None) -> list[dict]:
        """生成角度矩阵 = 卖点 × 人群 的笛卡尔积

        Args:
            selling_points: 卖点列表（如 ["高纤维", "低GI", "天然无添加"]）
            extra_audiences: 额外人群（从LLM扩展的）

        Returns:
            [{"angle_key": "高纤维×便秘人群", "selling_point": "...", "audience": "..."}, ...]
        """
        # 人群
        audiences = CATEGORY_AUDIENCES.get(
            self.category, CATEGORY_AUDIENCES["食品"])
        if extra_audiences:
            audiences = list(dict.fromkeys(extra_audiences + audiences))

        # 笛卡尔积
        angles = []
        for sp in selling_points:
            sp = sp.strip()
            if not sp or len(sp) < 2:
                continue
            # 简化卖点名称（取前12字）
            sp_short = sp[:12]
            for aud in audiences:
                aud = aud.strip()
                if not aud:
                    continue
                angles.append({
                    "angle_key": f"{sp_short}×{aud}",
                    "selling_point": sp_short,
                    "audience": aud,
                    "scene": "",  # 待LLM填充
                })

        self.angles = angles
        logger.info("创意矩阵: %d卖点 × %d人群 = %d角度",
                     len(selling_points), len(audiences), len(angles))
        return angles

    def select(self, n: int = 5, product_id: str = "") -> list[dict]:
        """从矩阵中加权选择 n 个角度

        优先从未使用过的角度中选，已用过的指数衰减降权。
        """
        if not self.angles:
            return []

        from adflow.engine.angle_history import AngleHistory
        history = AngleHistory(product_id, self.product_name)

        selected = history.select_best(self.angles, n)
        return selected

    @staticmethod
    def build_prompt_context(selected: list[dict]) -> str:
        """构建注入prompt的角度上下文"""
        lines = ["## 创意角度分配（每个变体对应一个角度，禁止交叉使用）", ""]
        for i, a in enumerate(selected):
            lines.append(
                f"变体{i}: 卖点=[{a['selling_point']}] × 人群=[{a['audience']}]"
                + (f" 场景方向=[{a.get('scene', '')}]" if a.get('scene') else ""))
        lines.append("")
        lines.append("每个变体必须严格围绕分配的卖点和人群来写，不同变体之间不能交叉使用对方的卖点或人群。")
        return "\n".join(lines)
