"""
LLM Vision API 自动打标
- 从视频提取关键帧 → 发送给多模态 LLM → 解析标签 JSON
- 打标完成后自动更新素材数据库记录
"""

import json
import base64
import logging
import os

from openai import OpenAI

from adflow.config_loader import config
from adflow.engine.video_probe import VideoProbe

_log = logging.getLogger("adflow.tagger")


# 提示词模板
TAGGING_PROMPT = """你是一个专业的视频素材分析助手。请仔细观察这些从同一段视频中提取的关键帧，分析视频内容并输出 JSON。

请从以下维度对视频素材进行标注（每个维度的可选值见括号）：

1. scene（场景）：indoor_studio / indoor_home / indoor_office / indoor_kitchen / indoor_bathroom / indoor_store / indoor_gym / indoor_other / outdoor_street / outdoor_nature / outdoor_urban / green_screen
2. shot_type（景别）：extreme_closeup / closeup / medium_closeup / medium / medium_wide / wide / extreme_wide
3. camera_movement（运镜）：static / pan / tilt / zoom_in / zoom_out / tracking / handheld / aerial
4. emotion（情绪）：excited / happy / calm / serious / urgent / curious / trust / surprise / anxious / neutral
5. product_visibility（产品露出）：none / partial / full / packaging / usage / before_after / text_logo
6. has_person（有人物）：true / false
7. person_count（人数）：0 / 1 / 2 / 3-5 / 6-10 / 10+
8. person_role（人物身份）：host / customer / expert / actor / no_person
9. person_feature（人物特征，逗号分隔多项）：face_visible / hands_visible / full_body / group / single
10. has_dialogue（原片是否有对白）：true / false
11. lighting（光线）：natural / studio / bright / dim / backlit / warm / cool / high_contrast
12. pace（节奏）：fast / medium / slow
13. quality_flags（质量标记，逗号分隔多项）：clean / blurry / shaky / overexposed / underexposed / noisy / watermark
14. material_category（素材类型）：product_shoot / scenario_shoot / ugc_style / stock_footage / screen_record / animation / text_card
15. free_tags（自由标签数组，5-10个中文关键词描述画面内容）

请严格输出以下 JSON 格式（不要输出任何其他内容）：

```json
{
  "scene": "...",
  "shot_type": "...",
  "camera_movement": "...",
  "emotion": "...",
  "product_visibility": "...",
  "has_person": true/false,
  "person_count": "...",
  "person_role": "...",
  "person_feature": "...",
  "has_dialogue": true/false,
  "lighting": "...",
  "pace": "...",
  "quality_flags": "...",
  "material_category": "...",
  "free_tags": ["...", "..."]
}
```
"""


class AutoTagger:
    """LLM Vision 自动打标器"""

    def __init__(self, model: str | None = None):
        self.model = model or config.llm_model
        self.api_key = config.llm_api_key or os.environ.get("DASHSCOPE_API_KEY", "")
        self.base_url = config.llm_base_url

    def tag_material(self, material_id: str, file_path: str,
                     frame_dir: str | None = None) -> dict:
        """对单个素材自动打标，返回标签 dict"""
        frames: list[str] = []  # 提前初始化，避免 finally 块 UnboundLocalError
        try:
            # 1. 提取关键帧
            if frame_dir is None:
                frame_dir = os.path.join(
                    config.materials_dir, "_frames", material_id[:8])
            frames = VideoProbe.extract_key_frames(file_path, frame_dir, count=5)
            if not frames:
                raise RuntimeError(f"无法从视频提取关键帧: {file_path}")

            # 2. 编码图片
            images_base64 = []
            for fp in frames:
                with open(fp, "rb") as f:
                    images_base64.append(base64.b64encode(f.read()).decode("utf-8"))

            # 3. 构建多模态请求
            content_blocks = []
            for idx, img_b64 in enumerate(images_base64):
                content_blocks.append({
                    "type": "image_url",
                    "image_url": {"url": f"data:image/jpeg;base64,{img_b64}"},
                })
                content_blocks.append({
                    "type": "text",
                    "text": f"关键帧 {idx + 1}",
                })
            content_blocks.append({"type": "text", "text": TAGGING_PROMPT})

            # 4. 调用 API
            tags = self._call_llm(content_blocks)

            # 5. 更新数据库
            self._update_material_tags(material_id, tags)

            _log.info("打标完成: %s → %s",
                       os.path.basename(file_path),
                       ", ".join(tags.get("free_tags", [])[:5]))

        except Exception as e:
            _log.error("打标失败 %s: %s", os.path.basename(file_path), e)
            raise

        finally:
            # 清理临时帧
            if frames:
                for fp in frames:
                    try:
                        os.remove(fp)
                    except OSError:
                        pass

        return tags

    def _call_llm(self, content_blocks: list[dict]) -> dict:
        """调用多模态 LLM API（OpenAI 兼容格式）"""
        client = OpenAI(api_key=self.api_key, base_url=self.base_url)
        response = client.chat.completions.create(
            model=self.model,
            max_tokens=config.llm_max_tokens,
            temperature=0.3,  # 打标用低温度，更稳定
            messages=[{"role": "user", "content": content_blocks}],
        )

        # 解析响应中的 JSON
        raw = response.choices[0].message.content
        if raw is None:
            raise RuntimeError("LLM 返回空响应")
        return self._parse_tags(raw)

    @staticmethod
    def _parse_tags(raw_text: str) -> dict:
        """从 LLM 响应中提取 JSON"""
        # 尝试提取 ```json ... ``` 代码块
        if "```json" in raw_text:
            start = raw_text.index("```json") + 7
            end = raw_text.index("```", start)
            raw_text = raw_text[start:end]
        elif "```" in raw_text:
            start = raw_text.index("```") + 3
            end = raw_text.index("```", start)
            raw_text = raw_text[start:end]

        parsed = json.loads(raw_text.strip())

        # 标准化布尔值
        for bool_field in ("has_person", "has_dialogue"):
            if bool_field in parsed:
                val = parsed[bool_field]
                if isinstance(val, str):
                    parsed[bool_field] = val.lower() in ("true", "yes", "是")
                else:
                    parsed[bool_field] = bool(val)

        # 标准化 person_count
        if "person_count" in parsed:
            parsed["person_count"] = str(parsed["person_count"])

        # 标准化 free_tags
        if "free_tags" in parsed:
            parsed["free_tags"] = list(parsed["free_tags"])
        else:
            parsed["free_tags"] = []

        return parsed

    @staticmethod
    def _update_material_tags(material_id: str, tags: dict) -> None:
        """将打标结果写入数据库"""
        from adflow.db.material_repo import MaterialRepo

        repo = MaterialRepo()

        # 更新结构化标签
        repo.update_auto_tags(
            material_id,
            scene=tags.get("scene", ""),
            shot_type=tags.get("shot_type", ""),
            camera_movement=tags.get("camera_movement", ""),
            emotion=tags.get("emotion", "neutral"),
            product_visibility=tags.get("product_visibility", "none"),
            has_person=tags.get("has_person", False),
            person_count=tags.get("person_count", "0"),
            person_role=tags.get("person_role", "no_person"),
            person_feature=tags.get("person_feature", ""),
            has_dialogue=tags.get("has_dialogue", False),
            lighting=tags.get("lighting", ""),
            pace=tags.get("pace", "medium"),
            quality_flags=tags.get("quality_flags", "clean"),
            material_category=tags.get("material_category", ""),
        )

        # 更新自由标签
        free_tags = tags.get("free_tags", [])
        if free_tags:
            repo.update_tags(material_id, free_tags)

        # 更新质量评分
        from adflow.tagger.quality_scorer import score_quality
        # 需要先获取素材的分辨率和时长信息
        material = repo.get_by_id(material_id)
        if material:
            qr = score_quality(
                width=material.width, height=material.height,
                duration_ms=material.duration_ms,
                has_audio=True,  # 打标时粗略假设有音频
                quality_flags=tags.get("quality_flags", "clean"),
            )
            repo.update_auto_tags(material_id, auto_quality_score=qr.total_score)


def tag_material_sync(material_id: str, file_path: str) -> dict:
    """同步方式打标（便捷函数）"""
    tagger = AutoTagger()
    return tagger.tag_material(material_id, file_path)
