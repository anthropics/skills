# -*- coding: utf-8 -*-
"""把 Claude 写好的标签写入 AdFlow 素材库。

用法:
    python apply_tags.py               读 engine/data/keyframes/tags.json
    python apply_tags.py --file 路径   读指定文件

tags.json 格式（与引擎自动打标同构，字段值必须用下面这些枚举值）:
[
  {
    "material_id": "abc123",
    "scene": "indoor_home",          # indoor_studio/indoor_home/indoor_office/
                                     # indoor_kitchen/indoor_bathroom/indoor_store/
                                     # indoor_gym/indoor_other/outdoor_street/
                                     # outdoor_nature/outdoor_urban/green_screen
    "shot_type": "closeup",          # extreme_closeup/closeup/medium_closeup/
                                     # medium/medium_wide/wide/extreme_wide
    "camera_movement": "static",     # static/pan/tilt/zoom_in/zoom_out/tracking/
                                     # handheld/aerial
    "emotion": "happy",              # excited/happy/calm/serious/urgent/curious/
                                     # trust/surprise/anxious/neutral
    "product_visibility": "full",    # none/partial/full/packaging/usage/
                                     # before_after/text_logo
    "has_person": true,
    "person_count": "1",             # 0/1/2/3-5/6-10/10+
    "person_role": "host",           # host/customer/expert/actor/no_person
    "person_feature": "hands_visible",  # 逗号分隔: face_visible/hands_visible/
                                        # full_body/group/single
    "has_dialogue": false,
    "lighting": "natural",           # natural/studio/bright/dim/backlit/warm/
                                     # cool/high_contrast
    "pace": "medium",                # fast/medium/slow
    "quality_flags": "clean",        # 逗号分隔: clean/blurry/shaky/overexposed/
                                     # underexposed/noisy/watermark
    "material_category": "product_shoot",  # product_shoot/scenario_shoot/
                                           # ugc_style/stock_footage/
                                           # screen_record/animation/text_card
    "free_tags": ["产品特写", "开箱"]
  }
]
"""
import argparse
import json
import os
import sys

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")
sys.path.insert(0, ENGINE)

# 每个字段的合法值（None = 自由文本/逗号分隔，不校验枚举）
ENUMS = {
    "scene": {"indoor_studio", "indoor_home", "indoor_office", "indoor_kitchen",
              "indoor_bathroom", "indoor_store", "indoor_gym", "indoor_other",
              "outdoor_street", "outdoor_nature", "outdoor_urban", "green_screen"},
    "shot_type": {"extreme_closeup", "closeup", "medium_closeup", "medium",
                  "medium_wide", "wide", "extreme_wide"},
    "camera_movement": {"static", "pan", "tilt", "zoom_in", "zoom_out",
                        "tracking", "handheld", "aerial"},
    "emotion": {"excited", "happy", "calm", "serious", "urgent", "curious",
                "trust", "surprise", "anxious", "neutral"},
    "product_visibility": {"none", "partial", "full", "packaging", "usage",
                           "before_after", "text_logo"},
    "person_role": {"host", "customer", "expert", "actor", "no_person"},
    "lighting": {"natural", "studio", "bright", "dim", "backlit", "warm",
                 "cool", "high_contrast"},
    "pace": {"fast", "medium", "slow"},
    "material_category": {"product_shoot", "scenario_shoot", "ugc_style",
                          "stock_footage", "screen_record", "animation",
                          "text_card"},
}
BOOLS = ("has_person", "has_dialogue")
DEFAULTS = {
    "scene": "", "shot_type": "", "camera_movement": "", "emotion": "neutral",
    "product_visibility": "none", "has_person": False, "person_count": "0",
    "person_role": "no_person", "person_feature": "", "has_dialogue": False,
    "lighting": "", "pace": "medium", "quality_flags": "clean",
    "material_category": "",
}


def clean_item(raw: dict) -> tuple[dict, list[str]]:
    """校验一条标签：非法枚举值换默认值并记警告。返回 (干净字段, 警告列表)"""
    fields, warns = {}, []
    for key, allowed in ENUMS.items():
        val = str(raw.get(key, "") or "").strip()
        if not val or val in allowed:
            fields[key] = val or DEFAULTS.get(key, "")
        else:
            fields[key] = DEFAULTS.get(key, "")
            warns.append("%s 值 %r 不在允许范围，已用默认 %r"
                         % (key, val, fields[key] or "空"))
    for key in BOOLS:
        val = raw.get(key)
        fields[key] = val if isinstance(val, bool) else bool(val)
    # 自由格式字段
    fields["person_count"] = str(raw.get("person_count", "0") or "0")
    fields["person_feature"] = str(raw.get("person_feature", "") or "")
    fields["quality_flags"] = str(raw.get("quality_flags", "clean") or "clean")
    tags = raw.get("free_tags", [])
    if not isinstance(tags, list):
        tags = [str(tags)]
    fields["_free_tags"] = [str(t).strip() for t in tags if str(t).strip()]
    return fields, warns


def main():
    ap = argparse.ArgumentParser(description="写入素材标签")
    ap.add_argument("--file", default=os.path.join(
        ENGINE, "data", "keyframes", "tags.json"), help="tags.json 路径")
    args = ap.parse_args()

    if not os.path.isfile(args.file):
        print("[X] 找不到标签文件: %s" % args.file)
        print("先让 Claude 看完关键帧写好这个文件")
        sys.exit(1)

    try:
        with open(args.file, encoding="utf-8") as f:
            items = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        print("[X] 标签文件读不出来（%s）— 让 Claude 检查 JSON 格式" % e)
        sys.exit(1)
    if not isinstance(items, list) or not items:
        print("[X] 标签文件是空的或格式不对（要一个 JSON 数组）")
        sys.exit(1)

    try:
        from adflow.db.material_repo import MaterialRepo
        from adflow.tagger.quality_scorer import score_quality
    except Exception as e:
        print("[X] 引擎依赖没装好（%s）— 先跑 python setup_env.py --deps" % e)
        sys.exit(1)

    repo = MaterialRepo()
    done, failed = 0, []
    for raw in items:
        mid = str(raw.get("material_id", "") or "")
        mat = repo.get_by_id(mid) if mid else None
        if not mat:
            failed.append("%s: 素材 ID 不存在" % (mid or "(空)"))
            continue
        fields, warns = clean_item(raw)
        for w in warns:
            print("  [警告] %s: %s" % (mid, w))
        free_tags = fields.pop("_free_tags")
        repo.update_auto_tags(mid, **fields)
        if free_tags:
            repo.update_tags(mid, free_tags)
        # 质量分回写（与引擎自动打标同口径）
        qr = score_quality(
            width=mat.width, height=mat.height,
            duration_ms=mat.duration_ms, has_audio=True,
            quality_flags=fields.get("quality_flags", "clean"))
        repo.update_auto_tags(mid, auto_quality_score=qr.total_score)
        done += 1
        print("[OK] %s (%s) 标签已写入" % (mid, mat.original_filename))

    print("-" * 40)
    print("完成: %d 条写入，%d 条失败" % (done, len(failed)))
    for msg in failed:
        print("  失败: " + msg)
    if done:
        print("下一步: python check_env.py 看素材库状态，然后让 Claude 写文案出片")
    sys.exit(0 if not failed else 1)


if __name__ == "__main__":
    main()
